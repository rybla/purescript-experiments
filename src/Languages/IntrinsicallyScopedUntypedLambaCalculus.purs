module Languages.IntrinsicallyScopedUntypedLambaCalculus where

import Prelude

import Data.Symbol (class IsSymbol)
import Prim.Row (class Cons)
import Type.Proxy (Proxy(..))

-- =============================================================================

data Term scope
  = Var (ExistsVar scope)
  | Lam (ExistsLam scope)
  | App (Term scope) (Term scope)

var x = Var (mkExistsVar x)
lam x b = Lam (mkExistsLam x b)
app f x = App f x

-- =============================================================================

foreign import data IntroKind :: Type
foreign import data Intro :: IntroKind

-- =============================================================================

newtype ExistsVar scope = ExistsVar (forall r. ExistsVarK scope r -> r)
type ExistsVarK scope r = forall x scope_. IsSymbol x => Cons x Intro scope_ scope => Proxy x -> r

mkExistsVar :: forall scope. ExistsVarK scope (ExistsVar scope)
mkExistsVar x = ExistsVar \k -> k x

runExistsVar :: forall scope r. ExistsVarK scope r -> ExistsVar scope -> r
runExistsVar k1 (ExistsVar k2) = k2 k1

-- =============================================================================

newtype ExistsLam scope = ExistsLam (forall r. ExistsLamK scope r -> r)
type ExistsLamK scope r = forall x scope'. IsSymbol x => Cons x Intro scope scope' => Proxy x -> Term scope' -> r

mkExistsLam :: forall scope. ExistsLamK scope (ExistsLam scope)
mkExistsLam x b = ExistsLam \k -> k x b

runExistsLam :: forall scope r. ExistsLamK scope r -> ExistsLam scope -> r
runExistsLam k1 (ExistsLam k2) = k2 k1

-- =============================================================================
-- Examples

_f = Proxy :: Proxy "f"
_x = Proxy :: Proxy "x"
_y = Proxy :: Proxy "y"
_z = Proxy :: Proxy "z"

x_term :: forall scope. Term (x :: Intro | scope)
x_term = var _x

y_term :: forall scope. Term (y :: Intro | scope)
y_term = var _y

id_term :: forall scope. Term scope
id_term = lam _x (var _x)

apply_term :: forall scope. Term scope
apply_term = lam _f (lam _x (app (var _f) (var _x)))

