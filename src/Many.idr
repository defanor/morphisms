import Common

-- the `many` isomorphism: roughly List a <-> List b, constructed with
-- a retraction Maybe a < List b which satisfies a couple of simple
-- and necessary additional restrictions:
-- 1. (x:a) -> (all (isNothing . r) $ prefixes $ f (Just x) = True)
-- 2. (l:List b) -> isJust (r l) = True -> (f (r l)) = l


snoc : (x : a) -> List a -> List a
snoc x [] = [x]
snoc x (y :: xs) = (y :: snoc x xs)

reverse' : List a -> List a
reverse' [] = []
reverse' (x :: xs) = (snoc x (reverse' xs))

suffixes : List a -> List (List a)
suffixes [] = []
suffixes (x::xs) = xs :: suffixes xs

prefixes : List a -> List (List a)
prefixes = (map reverse') . suffixes . reverse'

all' : (a -> Bool) -> List a -> Bool
all' p [] = True
all' p (x::xs) = p x && all' p xs


data MRetraction : (a : Type) -> (b : Type) -> (f : Maybe a -> List b) -> (r : List b -> Maybe a) -> Type where
  MkMRetraction : (f : Maybe a -> List b) ->
                (r : List b -> Maybe a) ->
                (v : (x : Maybe a) -> r (f x) = x) ->
                (np: (x:a) -> (all' (isNothing . r) $ prefixes $ f (Just x) = True)) ->
                (ji: (l:List b) -> isJust (r l) = True -> (f (r l)) = l) ->
                (en: isNothing . r $ [] = True) ->
                MRetraction a b f r


data Many : Type -> Type -> Type where
  Nil : MRetraction a b f r ->
      (l: List b) ->
      (all' (isNothing . r) $ l :: prefixes l = True) ->
      Many a b
  Cons : MRetraction a b f r ->
       a ->
       Many a b ->
       Many a b

-- ^ this should be isomorphic to regular lists. informal proof:

-- Firstly, there is a retraction (Maybe a) < (List b), such that for
-- any l:List b = f x:a, there's no prefixes (counting Nil) of l that
-- could be read as other `a` values, and hence no ambiguity after
-- concatenation.

-- Secondly, input that can't be parsed goes into Many's Nil, and any
-- data that goes into Cons could be restored (another requirement on
-- the retraction), hence no data from List gets lost.

-- Obviously, no ambiguity in Maybe a -> List a translation, and no
-- data gets lost on translation into the list. Except for retraction
-- and proofs, maybe, so not that obviously, but they are kinda fixed.


manyExtractFirst' : (r : b -> Maybe a) -> (l: List b) -> all' (isNothing . r) l = False -> a
manyExtractFirst' r [] prf = void $ trueNotFalse prf
manyExtractFirst' r (x :: xs) prf with (r x)
  | Nothing = manyExtractFirst' r xs prf
  | Just x = x

manyExtractFirst : (r : List b -> Maybe a) ->
                 (l: List b) ->
                 (all' (isNothing . r) $ l :: prefixes l = False) ->
                 (isNothing . r $ [] = True) ->
                 a
manyExtractFirst r l p n = manyExtractFirst' r (l :: prefixes l) p

many : MRetraction a b f r ->
     Iso (Many a b) (List b)
many {a=a} {b=b} (MkMRetraction f r v np ji en) = MkIso to from tf ft
  where
  to : Many a b -> List b
  to (Nil r l s) = l
  to (Cons (MkMRetraction f _ _ _ _ _) x s) = f (Just x) ++ to s
  from : List b -> Many a b
  from l = case (inspect $ all' (isNothing . r) $ l :: prefixes l) of
    (match True {eq=eq}) => Nil (MkMRetraction f r v np ji en) l eq
    (match False {eq=eq}) =>
           Cons (MkMRetraction f r v np ji en)
                (manyExtractFirst r l eq en)
                (from (assert_smaller l (drop (length (f (Just (manyExtractFirst r l eq en)))) l)))
  tf x = ?manytf
  ft x = ?manyft


-- `Many` without a tail

data Many' : Type -> Type -> Type where
  Nil' : MRetraction a b f r ->
       Many' a b
  Cons' : MRetraction a b f r ->
        a ->
        Many' a b ->
        Many' a b

isNil : Many a b -> Bool
isNil (Nil _ _ _) = True
isNil (Cons _ _ _) = False

mto' : Many a b -> Many' a b
mto' (Nil r l s) = Nil' r
mto' (Cons r x m) = Cons' r x (mto' m)

mfrom' : Many' a b -> Many a b
mfrom' (Nil' (MkMRetraction f r v np ji en)) = Nil (MkMRetraction f r v np ji en) [] (rewrite en in Refl)
mfrom' (Cons' r x m) = Cons r x (mfrom' m)

mtail : Many a b -> List b
mtail (Cons _ _ m) = mtail m
mtail (Nil _ l _) = l

manyAnd : (mi: Iso (Many a b) (List b)) ->
        (cr: Retraction c (List b) cto cfrom) ->
        ((x:c) -> (isNil (unappIso mi (cto x)) = True)) ->
        ((l:List b) -> (isNil (unappIso mi l) = True) -> (cto (cfrom l) = l)) ->
        Iso (Many' a b, c) (List b)
manyAnd {a=a} {b=b} (MkIso mto mfrom mtf mft) (MkRetraction cto cfrom cft) p p2 = MkIso to from tf ft
  where
  to : (Many' a b, c) -> List b
  to (x, y) = mto (mfrom' x) ++ cto y
  from : List b -> (Many' a b, c)
  from l = case (mfrom l) of
    m => (mto' m, cfrom (mtail m))
  tf x = ?mvtf -- rewrite (ctf (mtail (mfrom x))) in ?mvtf
  ft x = ?mvft





-- examples


data Foo = Zero | One | End

bcto' : List Bool -> List Foo
bcto' [] = [End]
bcto' (False::xs) = Zero :: bcto' xs
bcto' (True::xs) = One :: bcto' xs

bcto : Maybe (List Bool) -> List Foo
bcto Nothing = []
bcto (Just l) = bcto' l

bcfrom : List Foo -> Maybe (List Bool)
bcfrom (Zero::xs) = do
  rest <- bcfrom xs
  Just (False :: rest)
bcfrom (One::xs) = do
  rest <- bcfrom xs
  Just (True :: rest)
bcfrom [End] = Just []
bcfrom _ = Nothing

boolFoo : MRetraction (List Bool) Foo bcto bcfrom
boolFoo = MkMRetraction bcto bcfrom v np ji en
  where
    v' : (l: List Bool) -> bcfrom (bcto' l) = Just l
    v' [] = Refl
    v' (False :: xs) = rewrite (v' xs) in Refl
    v' (True :: xs) = rewrite (v' xs) in Refl
    v : (l: Maybe (List Bool)) -> bcfrom (bcto l) = l
    v Nothing = Refl
    v (Just l) = v' l
    np x = believe_me ()
    ji l p = believe_me ()
    en = Refl

bsto : Bool -> Foo
bsto True = One
bsto False = Zero

bsfrom : Foo -> Bool
bsfrom End = False
bsfrom Zero = False
bsfrom One = True

boolFooS : Retraction (List Bool) (List Foo) (map bsto) (map bsfrom)
boolFooS = MkRetraction (map bsto) (map bsfrom) v
  where
  v [] = Refl
  v (False :: xs) = cong (v xs)
  v (True :: xs) = cong (v xs)

bfnbf : Iso (Many' (List Bool) Foo, List Bool) (List Foo)
bfnbf = manyAnd (many boolFoo) boolFooS p1 p2
  where
  -- ((x:List Bool) -> (isNil (unappIso (many boolFoo) (bsto x)) = True))
  -- there's never `End` in `bsto`, so it's `Nil`
  p1 = believe_me ()
  -- ((l:List b) -> (isNil (unappIso (many boolFoo) l) = True) -> (bsto (bsfrom l) = l))
  -- `Nil` happens only if there's no `End`, and in that case `bsto (bsfrom l) = l`
  p2 = believe_me ()


lfNil : Many (List Bool) Foo
lfNil = Nil boolFoo [] Refl

lfCons : List Bool -> Many (List Bool) Foo -> Many (List Bool) Foo
lfCons l m = Cons boolFoo l m

lfTest : Many (List Bool) Foo
lfTest =
       lfCons [True, False, True, True] $
              lfCons [True, True] $
                     lfCons [False, False] $
                            lfNil

-- λΠ> appIso (many boolFoo) lfTest
-- [One, Zero, One, One, End, One, One, End, Zero, Zero, End] : List Foo
-- λΠ> appIso (many boolFoo) $ unappIso (many boolFoo) [One, Zero, One, One, End, One, One, End, Zero, Zero]
-- [One, Zero, One, One, End, One, One, End, Zero, Zero] : List Foo
-- λΠ> appIso bfnbf ((mto' lfTest), [True, False])
-- [One, Zero, One, One, End, One, One, End, Zero, Zero, End, One, Zero] : List Foo
