module Typeclasses.PeanoArithmetic where

import Prelude

import Effect (Effect)
import Effect.Class.Console as Console
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

foreign import data Nat :: Type
foreign import data Zero :: Nat
foreign import data Suc :: Nat -> Nat

type One = Suc Zero
type Two = Suc One
type Three = Suc Two
type Four = Suc Three

--------------------------------------------------------------------------------
-- ReifyNat
--------------------------------------------------------------------------------

class ReifyNat (n :: Nat) where
  reifyNat :: Proxy n -> Int

instance ReifyNat Zero where
  reifyNat _ = 0

instance ReifyNat n => ReifyNat (Suc n) where
  reifyNat _ = 1 + reifyNat (Proxy :: Proxy n)

--------------------------------------------------------------------------------
-- Add
--------------------------------------------------------------------------------

class Add (m :: Nat) (n :: Nat) (add_m_n :: Nat) | m n -> add_m_n

-- 0 + n = n
instance Add Zero n n
-- (1 + m) + n = 1 + (m + n)
instance Add m n add_m_n => Add (Suc m) n (Suc add_m_n)

example_Add :: Int
example_Add = reifyNat (Proxy :: forall n. Add One Two n => ReifyNat n => Proxy n)

--------------------------------------------------------------------------------
-- Mul
--------------------------------------------------------------------------------

class Mul (m :: Nat) (n :: Nat) (mul_m_n :: Nat) | m n -> mul_m_n

-- 0 * n = n
instance Mul Zero n Zero
-- (1 + m)*n = n + m*n
instance (Mul m n mul_m_n, Add n mul_m_n add_n_mul_m_n) => Mul (Suc m) n add_n_mul_m_n

example_Mul :: Int
example_Mul = reifyNat (Proxy :: forall n. Mul Two Two n => ReifyNat n => Proxy n)

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: Effect Unit
main = do
  Console.log ("example_Add = " <> show example_Add)
  Console.log ("example_Mul = " <> show example_Mul)

