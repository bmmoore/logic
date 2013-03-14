module Logic.Types where

newtype Var = Var String
  deriving Show
newtype Function = Function String
  deriving Show
newtype Predicate = Predicate String
  deriving Show

data Term = Term Function [Term] | VarTerm Var
  deriving Show
data Atom = Atom Predicate [Term]
  deriving Show

data Formula =
    Atomic Atom
  | Not Formula
  | And Formula Formula
  | Or  Formula Formula
  | Forall Var Formula
  | Exists Var Formula
  deriving Show