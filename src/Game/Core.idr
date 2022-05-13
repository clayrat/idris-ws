module Game.Core

%default total

-- Games

data MovEnc : Type where
  Nil : MovEnc
  One : MovEnc
  Plus : MovEnc -> MovEnc -> MovEnc
  Ntm : MovEnc -> MovEnc

public export
T : MovEnc -> Type
T Nil        = Void
T One        = Unit
T (Plus x y) = Either (T x) (T y)
T (Ntm m)    = (Nat, T m)

public export
data Game : Type where
  Gam : {i : MovEnc} -> (T i -> Game) -> Game

public export
mvEnc : Game -> MovEnc
mvEnc (Gam {i} f) = i

public export
Mov : Game -> Type
Mov g = T (mvEnc g)

public export
rest : (g : Game) -> Mov g -> Game
rest (Gam f) m = f m

-- Constructions on Games

public export
I : Game
I = Gam {i=Nil} (\v => void v)

public export
sumfun : {0 a, b : Type} -> {0 c : Either a b -> Type} ->
         (f : (x : a) -> c (Left x)) ->
         (g : (x : b) -> c (Right x)) ->
         (x : Either a b) -> c x
sumfun f g (Left x)  = f x
sumfun f g (Right y) = g y

public export
prod : Game -> Game -> Game
prod (Gam {i} f) (Gam {i=j} g) = Gam {i = Plus i j} (sumfun f g)

omg : Game -> Game
omg (Gam {i} f) = Gam {i = Ntm i} (\x => f (snd x))

mutual
  public export
  lolli : Game -> Game -> Game
  lolli g (Gam {i} f) = Gam {i} (\j => ten (f j) g)

  public export
  sequo : Game -> Game -> Game
  sequo (Gam {i} f) h = Gam {i} (\j => lolli h (f j))

  public export
  ten : Game -> Game -> Game
  ten g h = prod (sequo g h) (sequo h g)

one : Game
one = Gam {i=One} (\() => I)

toOne : Game -> Game
toOne g = Gam {i=One} (\() => g)

slolli : Game -> Game -> Game
slolli g (Gam {i} f) = Gam {i} (\j => sequo g (f j))

-- Strategies

data Pol = P | N

data Strat : Pol -> Game -> Type where
  Pos : {0 g : Game} -> (i : Mov g) -> Strat N (rest g i) -> Strat P g
  Neg : {0 g : Game} -> ((i : Mov g) -> Strat P (rest g i)) -> Strat N g

-- Game morphisms

public export
data Mor : Game -> Game -> Type where
  Sim : {0 a, b : Game} ->
        (h : Mov b -> Mov a) ->
        ((j : Mov b) -> Mor (rest b j) (rest a (h j))) ->
        Mor a b

morId : {0 g : Game} -> Mor g g
morId {g = Gam f} = Sim id (\i => morId {g = f i})

morTrans : {0 a, b, c : Game} -> Mor b c -> Mor a b -> Mor a c
morTrans (Sim f f') (Sim g g') = Sim (g . f) (\x => morTrans (g' (f x)) (f' x))

public export
data Iso : Game -> Game -> Type where
  Bsm : {0 a, b : Game} -> Mor b a -> Mor a b -> Iso a b

isoId : {0 g : Game} -> Iso g g
isoId = Bsm morId morId

isoTrans : {0 a, b, c : Game} -> Iso a b -> Iso b c -> Iso a c
isoTrans (Bsm s s') (Bsm r r') = Bsm (morTrans s r) (morTrans r' s')

isoRev : {0 m, n : Game} -> Iso m n -> Iso n m
isoRev (Bsm f g) = Bsm g f

public export
wk1 : {0 m, n : Game} -> Iso m n -> Mor m n
wk1 (Bsm _ g) = g

public export
wk2 : {0 m, n : Game} -> Iso m n -> Mor n m
wk2 (Bsm f _) = f

mutual
  morCompL : {0 m, n : Game} -> Mor n m -> Strat N n -> Strat N m
  morCompL (Sim h h') (Neg f) = Neg (\i => morCompR (f (h i)) (h' i))

  morCompR : {0 p, q : Game} -> Strat P p -> Mor q p -> Strat P q
  morCompR (Pos m g) (Sim h h') = Pos (h m) (morCompL (h' m) g)

isoCompL : {0 m, n : Game} -> Iso m n -> Strat N m -> Strat N n
isoCompL g s = morCompL (wk1 g) s

isoCompR :  {0 p, q : Game} -> Strat P p -> Iso p q -> Strat P q
isoCompR s f = morCompR s (wk2 f)
