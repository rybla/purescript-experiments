module Languages.IntrinsicallyTypedLambdaCalculus where

import Prelude hiding (($), type (~>))

import Data.Symbol (class IsSymbol)
import Prim.Row (class Cons)
import Type.Proxy (Proxy(..))

-- =============================================================================

foreign import data Ty :: Type
foreign import data Arr :: Ty -> Ty -> Ty

infixr 7 type Arr as ~>

class IsArr (ty :: Ty) (a :: Ty) (b :: Ty) | ty -> a b

instance IsArr (Arr a b) a b

-- =============================================================================

data Term (a :: Ty) (ctx :: Row Ty)
  = Var (ExistsVar a ctx)
  | Lam (ExistsLam a ctx)
  | LamAnn (ExistsLamAnn a ctx)
  | App (ExistsApp a ctx)

infix 6 type Term as -|

var :: forall x a ctx ctx_. IsSymbol x => Cons x a ctx_ ctx => Proxy x -> (a -| ctx)
var x = Var (mkExistsVar x)

lam :: forall x a b ctx ctx'. IsSymbol x => Cons x a ctx ctx' => Proxy x -> (b -| ctx') -> (a ~> b -| ctx)
lam x b = Lam (mkExistsLam x b)

infixr 5 lam as ~>

lamAnn :: forall x a b ctx ctx'. IsSymbol x => Cons x a ctx ctx' => Proxy x -> Proxy a -> (b -| ctx') -> (a ~> b -| ctx)
lamAnn x a b = LamAnn (mkExistsLamAnn x a b)

app :: forall a b ctx. (a ~> b -| ctx) -> (a -| ctx) -> (b -| ctx)
app f a = App (mkExistsApp f a)

infixr 6 app as $

-- =============================================================================

newtype ExistsVar (a :: Ty) (ctx :: Row Ty) = ExistsVar (forall r. ExistsVarK a ctx r -> r)
type ExistsVarK (a :: Ty) (ctx :: Row Ty) r = forall x ctx_. IsSymbol x => Cons x a ctx_ ctx => Proxy x -> r

mkExistsVar :: forall a ctx. ExistsVarK a ctx (ExistsVar a ctx)
mkExistsVar x = ExistsVar \k -> k x

runExistsVar :: forall a ctx r. ExistsVarK a ctx r -> ExistsVar a ctx -> r
runExistsVar k1 (ExistsVar k2) = k2 k1

-- =============================================================================

newtype ExistsLam a ctx = ExistsLam (forall r. ExistsLamK a ctx r -> r)

type ExistsLamK :: Ty -> Row Ty -> Type -> Type
type ExistsLamK ty ctx r = forall ctx' x a b. IsSymbol x => IsArr ty a b => Cons x a ctx ctx' => Proxy x -> (b -| ctx') -> r

mkExistsLam :: forall a ctx. ExistsLamK a ctx (ExistsLam a ctx)
mkExistsLam x b = ExistsLam \k -> k x b

runExistsLam :: forall a ctx r. ExistsLamK a ctx r -> ExistsLam a ctx -> r
runExistsLam k1 (ExistsLam k2) = k2 k1

-- =============================================================================

newtype ExistsLamAnn a ctx = ExistsLamAnn (forall r. ExistsLamAnnK a ctx r -> r)

type ExistsLamAnnK :: Ty -> Row Ty -> Type -> Type
type ExistsLamAnnK ty ctx r = forall ctx' x a b. IsSymbol x => IsArr ty a b => Cons x a ctx ctx' => Proxy x -> Proxy a -> (b -| ctx') -> r

mkExistsLamAnn :: forall a ctx. ExistsLamAnnK a ctx (ExistsLamAnn a ctx)
mkExistsLamAnn x a b = ExistsLamAnn \k -> k x a b

runExistsLamAnn :: forall a ctx r. ExistsLamAnnK a ctx r -> ExistsLamAnn a ctx -> r
runExistsLamAnn k1 (ExistsLamAnn k2) = k2 k1

-- =============================================================================

newtype ExistsApp a ctx = ExistsApp (forall r. ExistsAppK a ctx r -> r)
type ExistsAppK b ctx r = forall a. (a ~> b -| ctx) -> (a -| ctx) -> r

mkExistsApp :: forall a ctx. ExistsAppK a ctx (ExistsApp a ctx)
mkExistsApp f a = ExistsApp \k -> k f a

runExistsApp :: forall a ctx r. ExistsAppK a ctx r -> ExistsApp a ctx -> r
runExistsApp k1 (ExistsApp k2) = k2 k1

-- =============================================================================

_f = Proxy :: Proxy "f"
_x = Proxy :: Proxy "x"
_y = Proxy :: Proxy "y"
_z = Proxy :: Proxy "z"

x :: forall a ctx. a -| (x :: a | ctx)
x = var _x

y = var _y
z = var _z
f = var _f

a_useless_function :: forall a b ctx. a ~> b -| (y :: b | ctx)
a_useless_function = _x ~> y

id_term :: forall a ctx. a ~> a -| ctx
id_term = _x ~> x

apply_term :: forall ctx a b. (a ~> b) ~> a ~> b -| ctx
apply_term = _f ~> _x ~> f $ x

i :: forall a ctx. a ~> a -| ctx
i = _x ~> x

k :: forall a b ctx. a ~> (b ~> a) -| ctx
k = _x ~> _y ~> x

s :: forall a b c ctx. (a ~> b) ~> ((c ~> a) ~> c) ~> ((c ~> a) ~> b) -| ctx
s = _x ~> _y ~> _z ~> x $ z $ (y $ z)

sksk :: forall a b ctx. ((a ~> b) ~> a) ~> ((a ~> b) ~> (((b ~> b) ~> b) ~> ((b ~> b) ~> (b ~> b)))) -| ctx
sksk = s $ k $ s $ k

