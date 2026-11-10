-- What an interface carries besides names and types: the functions with bounds a module exports, as templates
module Elaboration
    ( Template (..)
    , Ctx (..)
    , functionType
    , isRefType
    , arrayElement
    ) where

import Data.Map (Map)

import Syntax
import Types

data Template = Template
    { tmplBounds :: [Bound]
    , tmplCtx :: Ctx
    , tmplParams :: [Variable]
    , tmplSignature :: Signature
    , tmplRequires :: [ValidationStatement]
    , tmplEnsures :: [ValidationStatement]
    , tmplTermination :: Maybe Termination
    , tmplBody :: [Statement]
    }
    deriving (Show, Eq)

data Ctx = Ctx
    { ctxFns :: Map Variable Type
    , ctxReturn :: Maybe Type
    }
    deriving (Show, Eq)

functionType :: [Variable] -> [Variable] -> [Type] -> Type -> Type
functionType [] [] ptys rty = TFn ptys rty
functionType sizes types ptys rty = TForall sizes types (TFn ptys rty)

isRefType :: Type -> Bool
isRefType (TRef _) = True
isRefType (TMutRef _) = True
isRefType _ = False

-- What an array can hold: any value that has a size and is not a function: an Int, a Bool, a list, a struct, an enum, a Box or an array.
-- A type not known yet is accepted: the lowering looks at the finished types.
arrayElement :: Type -> Bool
arrayElement ty = case ty of
    TFn{} -> False
    TForall{} -> False
    TRef{} -> False
    TMutRef{} -> False
    TArrayOf t _ -> arrayElement t
    _ -> True
