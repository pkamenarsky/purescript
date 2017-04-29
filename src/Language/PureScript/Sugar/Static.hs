module Language.PureScript.Sugar.Static (desugarStaticModule) where

import           Prelude.Compat

import           Control.Monad.Error.Class (MonadError(..))
import           Control.Monad.Supply.Class
import           Control.Monad.Trans.State
import           Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Data.Text as T
import           Language.PureScript.AST
import           Language.PureScript.Errors
import           Language.PureScript.Names
import           Language.PureScript.Environment
import           Language.PureScript.PSString


mkPtr :: Int -> PSString
mkPtr ptr = mkString $ T.pack $ "static_ptr_" ++ show ptr

-- |
-- Replaces all `static expr` applications with `StaticPtr module unique_id` and
-- builds up a `static_ptr_table` object per module.
--
desugarStaticModule :: forall m. (MonadSupply m, MonadError MultipleErrors m) => Module -> m Module
desugarStaticModule (Module ss coms mn ds exts) = do
  (ds', table) <- runStateT (parU ds $ desugarStatic mn) M.empty
  if M.null table
    then return $ Module ss coms mn ds' exts
    else return $ Module ss coms mn (tableDecl table:ds') ((ValueRef (Ident "static_ptr_table"):) <$> exts)
  where
  tableDecl :: M.Map Int Expr -> Declaration
  tableDecl table = ValueDeclaration (Ident "static_ptr_table") Public [] [GuardedExpr [] (tableExpr table)]

  tableExpr :: M.Map Int Expr -> Expr
  tableExpr table = Literal $ ObjectLiteral [ (mkPtr ptr, expr) | (ptr, expr) <- M.toList table ]

desugarStatic :: forall m. (MonadSupply m, MonadError MultipleErrors m) => ModuleName -> Declaration -> StateT (M.Map Int Expr) m Declaration
desugarStatic mn (PositionedDeclaration pos com d) = PositionedDeclaration pos com <$> rethrowWithPosition pos (desugarStatic mn d)
desugarStatic mn d = do
  let (f, _, _) = everywhereOnValuesM return replace return
  f d
  where
  replace :: Expr -> StateT (M.Map Int Expr) m Expr
  -- replace (PositionedValue p v (App (PositionedValue _ _ (Var (Qualified (Just (ModuleName [ProperName "Static"])) (Ident "static")))) expr)) = do
  replace (PositionedValue p v (App (PositionedValue _ _ (Var (Qualified _n (Ident "static")))) expr)) = do
    table <- get
    let ptr = (fromMaybe (-1) $ fst <$> M.lookupLE maxBound table) + 1
    modify $ M.insert ptr expr
    return $ PositionedValue p v
      $ Constructor (Qualified (Just $ moduleNameFromString "Static") (ProperName "StaticPtr"))
      `App` (Literal $ StringLiteral $ mkString $ runModuleName mn)
      `App` (Literal $ StringLiteral $ mkPtr ptr)
  replace (PositionedValue pos com v) = PositionedValue pos com <$> rethrowWithPosition pos (replace v)
  replace other = return other
