{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Intensional
    ( plugin
    ) where

import           BinIface
import           Binary
import           Control.Monad
import           Data.Bifunctor                 ( first )
import qualified Data.List                     as List
import qualified Data.Map                      as Map
import           Data.Map                       ( Map )
import           Display
import           GhcPlugins
import           IfaceEnv
import           IfaceSyn
import           Intensional.Constraints
import qualified Intensional.Horn.InferCoreExpr
                                               as Horn
import qualified Intensional.Horn.Monad        as Horn
import qualified Intensional.InferCoreExpr     as Sets
import           Intensional.InferM
import qualified Intensional.InferM            as Sets
import           Intensional.Scheme
import           Intensional.Types
import           Lens.Micro
import           Lens.Micro.Extras
import           NameCache                      ( OrigNameCache )
import           OccName
import           Pretty                         ( Mode(..) )
import           System.CPUTime
import qualified System.Console.Haskeline      as Haskeline
import           System.Directory
import           System.IO
import           TcIface
import           TcRnMonad
import           ToIface
import           TyCoRep

{-| 
  The GHC plugin is hardwired as @plugin@.  
-}
plugin :: Plugin
plugin = defaultPlugin { pluginRecompile = recomp, installCoreToDos = install }
  where
    recomp cmd =
        return $ if "force" `elem` cmd then ForceRecompile else NoForceRecompile
    todoPrefix cmd =
        [ CoreDoStrictness
        , -- it is useful to know what is bottom for the purpose of pattern failures
          CoreDoPluginPass "Intensional" (inferGuts cmd)
        ]
    install cmd todo = return (todoPrefix cmd ++ todo)

{-|
    Given a module name @m@, @interfaceName m@ is the file path
    that will be written with the corresponding serialised typings.
-}
interfaceName :: ModuleName -> FilePath
interfaceName = ("interface/" ++) . moduleNameString

inferGuts :: [CommandLineOption] -> ModGuts -> CoreM ModGuts
inferGuts cmd guts@ModGuts { mg_deps = d, mg_module = m, mg_binds = p } = do
    when ("debug-core" `elem` cmd) $ pprTraceM "Core Source:" $ ppr p
    che    <- getOrigNameCache
    dflags <- getDynFlags

    let useSetConstrs = True
    -- Reload saved typeschemes
    envHorn <- reloadSaved "Horn"
    envSets <- reloadSaved "Set"

    if useSetConstrs
        then liftIO $ do
            t0 <- getCPUTime
            -- Infer constraints
            let (!gamma, !errs, !stats) =
                    Sets.runInferM (Sets.inferProg p) m envSets
            t1 <- getCPUTime

            when ("time" `elem` cmd) $ recordBenchmarks
                (moduleNameString (moduleName m))
                (t0, t1)
                stats

            -- Display type errors
            let printErrLn = printSDocLn
                    PageMode
                    dflags
                    stderr
                    (setStyleColoured True $ defaultErrStyle dflags)

            forM_ errs
                $ \a -> when (m == modInfo a) (printErrLn $ showTypeError a)

            when (moduleNameString (moduleName m) `elem` cmd)
                $ repl (gamma Prelude.<> envSets) m p che

            -- Save typeschemes to interface file
            saveScheme "Set" gamma
        else liftIO $ do
            t0 <- getCPUTime
            -- Infer constraints
            let (!gamma, !errs, !stats) =
                    Horn.runInferM (Horn.inferProg p) m envHorn
            t1 <- getCPUTime

            when ("time" `elem` cmd) $ recordBenchmarks
                (moduleNameString (moduleName m))
                (t0, t1)
                stats

            -- Display type errors
            let printErrLn = printSDocLn
                    PageMode
                    dflags
                    stderr
                    (setStyleColoured True $ defaultErrStyle dflags)

            forM_ errs
                $ \a -> when (m == view (_cinfo . to prov) a)
                             (printErrLn $ showTypeError a)

            when (moduleNameString (moduleName m) `elem` cmd)
                $ repl (gamma Prelude.<> envHorn) m p che

            -- Save typeschemes to interface file
            saveScheme "Horn" gamma


    return guts

  where
    gbl = IfGblEnv { if_doc = text "initIfaceLoad", if_rec_types = Nothing }

    reloadSaved
        :: Binary con => FilePath -> CoreM (Map Name (SchemeGen con TyCon))
    reloadSaved suffix = do
        hask <- getHscEnv
        liftIO $ do
            initTcRnIf 'i' hask gbl (mkIfLclEnv m empty False) $ do
                cache <- mkNameCacheUpdater
                foldM
                    (\env (mod', _) -> do
                        let m_name = interfaceName mod' ++ suffix
                        exists <- liftIO $ doesFileExist m_name
                        if exists
                            then do
                                bh   <- liftIO $ readBinMem m_name
                                ictx <-
                                    liftIO
                                    $   Map.fromList
                                    <$> getWithUserData cache bh
                                ctx <- mapM (mapM tcIfaceTyCon) ictx
                                return (Map.union ctx env)
                            else return env
                    )
                    Map.empty
                    (dep_mods d)

    saveScheme
        :: Binary con => FilePath -> Map Name (SchemeGen con TyCon) -> IO ()
    saveScheme suffix gamma = do
        exist <- doesDirectoryExist "interface"
        bh    <- openBinMem (1024 * 1024)
        unless exist (createDirectory "interface")
        putWithUserData
            (const $ return ())
            bh
            (Map.toList $ Map.filterWithKey (\k _ -> isExternalName k)
                                            (fmap toIfaceTyCon <$> gamma)
            )
        writeBinMem bh (interfaceName (moduleName m) ++ suffix)

{-|
  When @cx@ is the type bindings for all the program so far and @md@
  is the currently processed module and @ch@ is GHC's name cache,
  @repl cx md ch@ is a read-eval-print-loop IO action, allowing the 
  user to inspect individual type bindings and output the raw core.
-}
repl
    :: (Refined con, Eq con, Monoid con)
    => BaseContext con
    -> Module
    -> CoreProgram
    -> OrigNameCache
    -> IO ()
repl cx md pr ch = Haskeline.runInputT Haskeline.defaultSettings loop
  where
    loop = do
        mbInput <- Haskeline.getInputLine (modn ++ "> ")
        case words <$> mbInput of
            Just [":q"]          -> return ()
            Just [":c", strName] -> do
                case mkName strName of
                    Just n
                        | Just e <- List.lookup
                            n
                            (map (first getName) $ flattenBinds pr)
                        -> Haskeline.outputStrLn $ showSDocUnsafe $ ppr e
                    _ -> return ()
                loop
            Just [":t", strName] -> do
                case mkName strName of
                    Just n | Just ts <- Map.lookup n cx ->
                        Haskeline.outputStrLn $ showSDocUnsafe $ typingDoc n ts
                    _ -> return ()
                loop
            _ -> loop
    typingDoc n ts = ppr n <+> colon <+> prpr (const empty) ts
    modn = moduleNameString (moduleName md)
    mkName s = lookupOrigNameCache ch m n
      where
        s'       = reverse s
        (n', m') = Prelude.span (/= '.') s'
        n        = mkOccName OccName.varName (reverse n')
        m        = if null m'
            then md
            else md { moduleName = mkModuleName $ reverse (drop 1 m') }

{-|
    Given a GHC interface tycon representation @iftc@,
    @tcIFaceTyCon iftc@ is the action that returns the original tycon.
-}
tcIfaceTyCon :: IfaceTyCon -> IfL TyCon
tcIfaceTyCon iftc = do
    e <- tcIfaceExpr (IfaceType (IfaceTyConApp iftc IA_Nil))
    case e of
        Type (TyConApp tc _) -> return tc
        _                    -> pprPanic "TyCon has been corrupted!" (ppr e)


