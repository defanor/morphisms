import Control.Isomorphism


-- probably useless
data Morphism : (a : Type) -> (b : Type) -> (f : a -> b) -> Type where
  MkMorphism : (f : a -> b) ->
               Morphism a b f

-- retraction for f
data Retraction : (a : Type) -> (b : Type) -> (f : a -> b) -> (r : b -> a) -> Type where
  MkRetraction : (f : a -> b) ->
                 (r : b -> a) ->
                 (v : (x : a) -> r (f x) = x) ->
                 Retraction a b f r

-- section for f
data Section : (a : Type) -> (b : Type) -> (f : a -> b) -> (s : b -> a) -> Type where
  MkSection : (f : a -> b) ->
              (s : b -> a) ->
              (v : (y : b) -> f (s y) = y) ->
              Section a b f s

-- retraction + section
data Isomorphism : (a : Type) -> (b : Type) -> Type where
  MkIsomorphism : {f : a -> b} ->
                  (r : Retraction a b f r') ->
                  (s : Section a b f s') ->
                  Isomorphism a b

uniquenessOfInverses : Retraction a b f r -> Section a b f s -> (x : b) -> r x = s x
uniquenessOfInverses (MkRetraction f r rv) (MkSection f s sv) x =
  -- s x = r x
  rewrite (sym $ sv x) in
  -- r (f (s x)) = s (f (s x))
  rewrite (rv (s x)) in
  -- s x = s (f (s x))
  rewrite (sv x) in
  -- s x = s x
  Refl

toIso : Isomorphism a b -> Iso a b
toIso (MkIsomorphism (MkRetraction f r rv) (MkSection f s sv)) =
  MkIso f s sv (\x => rewrite (sym $ uniquenessOfInverses (MkRetraction f r rv) (MkSection f s sv) (f x)) in (rv x))


eitherBool : Iso (Either a a) (a, Bool)
eitherBool = MkIso to from tf ft
  where
    to : (Either a a) -> (a, Bool)
    to (Left x) = (x, False)
    to (Right x) = (x, True)
    from : (a, Bool) -> (Either a a)
    from (x, False) = Left x
    from (x, True) = Right x
    tf (a, False) = Refl
    tf (a, True) = Refl
    ft (Left x) = Refl
    ft (Right x) = Refl


dec : (pc: a -> Type) -> (f : (x: a) -> Dec (pc x)) -> Iso (Sigma a (\x => Dec (pc x))) a
dec pc f = MkIso to from tf ft
  where
    to : (Sigma a (\x => Dec (pc x))) -> a
    to (MkSigma x p) = x
    from : a -> (Sigma a (\x => Dec (pc x)))
    from x = MkSigma x (f x)
    tf x = Refl
    ft (MkSigma x (Yes prf)) with (f x)
      | Yes prf = cong {f=\r => MkSigma x (Yes r)} $ believe_me ()
      | No contra = void $ contra prf
    ft (MkSigma x (No contra)) with (f x)
      | Yes prf = void $ contra prf
      | No contra = cong {f=\r => MkSigma x (No r)} $ believe_me ()


eitherDec : (pc: a -> Type) -> Iso (Sigma a (\x => Dec (pc x))) (Sigma a (\x => (Either (pc x -> Void) (pc x))))
eitherDec pc = MkIso to from tf ft
  where
    to : (Sigma a (\x => Dec (pc x))) -> (Sigma a (\x => (Either (pc x -> Void) (pc x))))
    to (MkSigma x (No contra)) = (x ** Left contra)
    to (MkSigma x (Yes prf)) = (x ** Right prf)
    from : (Sigma a (\x => (Either (pc x -> Void) (pc x)))) -> (Sigma a (\x => Dec (pc x)))
    from (MkSigma x (Left contra)) = (x ** No contra)
    from (MkSigma x (Right prf)) = (x ** Yes prf)
    tf (MkSigma x (Left contra)) = Refl
    tf (MkSigma x (Right prf)) = Refl
    ft (MkSigma x (No contra)) = Refl
    ft (MkSigma x (Yes prf)) = Refl


eitherSigmaDistribLeft : Iso (Sigma a (\x => (Either pa pb)))
                             (Either (Sigma a (\x => pa)) (Sigma a (\x => pb)))
eitherSigmaDistribLeft = MkIso to from tf ft
  where
    to : (Sigma a (\x => (Either pa pb))) -> (Either (Sigma a (\x => pa)) (Sigma a (\x => pb)))
    to (MkSigma x (Left pa)) = Left (MkSigma x pa)
    to (MkSigma x (Right pb)) = Right (MkSigma x pb)
    from : (Either (Sigma a (\x => pa)) (Sigma a (\x => pb))) -> (Sigma a (\x => (Either pa pb)))
    from (Left (MkSigma x pa)) = MkSigma x (Left pa)
    from (Right (MkSigma x pb)) = MkSigma x (Right pb)
    tf (Left (MkSigma x p)) = Refl
    ft (MkSigma x (Left pa)) = Refl
    ft (MkSigma x (Right pb)) = Refl


appIso : Iso a b -> a -> b
appIso (MkIso to _ _ _) x = to x

unappIso : Iso a b -> b -> a
unappIso (MkIso _ from _ _) x = from x


-- use a to find whether it's b or c next to it
branch : (pc: a -> Type) ->
       ((x: a) -> Dec (pc x)) ->
       Iso b d ->
       Iso c d ->
       Iso (Sigma a (\x => (Either (pc x -> Void, b) (pc x, c)))) (a, d)
branch pc
       f
       (MkIso bdto bdfrom bdtf bdft)
       (MkIso cdto cdfrom cdtf cdft)
       = MkIso to from tf ft
  where
    to : (Sigma a (\x => (Either (pc x -> Void, b) (pc x, c)))) -> (a, d)
    to (MkSigma x (Left (p, y))) = (x, bdto y)
    to (MkSigma x (Right (p, y))) = (x, cdto y)
    from : (a, d) -> (Sigma a (\x => (Either (pc x -> Void, b) (pc x, c))))
    from (x, y) = case (appIso (eitherDec pc) (unappIso (dec pc f) x)) of
      (MkSigma z (Left p)) => MkSigma z $ Left (p, bdfrom y)
      (MkSigma z (Right p)) => MkSigma z $ Right (p, cdfrom y)
    tf (x, y) with (f x)
      | Yes prf = rewrite (cdtf y) in Refl
      | No contra = rewrite (bdtf y) in Refl
    ft (MkSigma x (Left (p, y))) with (f x)
      | Yes prf = void $ p prf
      | No contra = rewrite (bdft y) in cong {f=\r => MkSigma x (Left (r, y))} $ believe_me ()
    ft (MkSigma x (Right (p, y))) with (f x)
      | Yes prf = rewrite (cdft y) in cong {f=\r => MkSigma x (Right (r, y))} $ believe_me ()
      | No contra = void $ contra p


list : Iso a b -> Iso (List a) (List b)
list (MkIso abto abfrom abtf abft) = MkIso to from tf ft
  where
    to : List a -> List b
    to [] = []
    to (x :: xs) = abto x :: to xs
    from : List b -> List a
    from [] = []
    from (x :: xs) = abfrom x :: from xs
    tf [] = Refl
    tf (x :: xs) = rewrite (abtf x) in cong (tf xs)
    ft [] = Refl
    ft (x :: xs) = rewrite (abft x) in cong (ft xs)

data Inspect : a -> Type where
  wi : {A : Type} -> (x : A) -> (y : A) -> (eq: x = y) -> Inspect x

inspect : {A : Type} -> (x : A) -> Inspect x
inspect x = wi x _ Refl

match : {A : Type} -> {x : A} -> (y : A) -> {eq : x = y} -> Inspect x
match y {eq} = wi _ y eq

dep_to : Iso b c -> a -> b -> (a, c)
dep_to (MkIso to' from' tf' ft') x y = (x, (to' y))

dep_from : Iso b c -> a -> c -> (a, b)
dep_from (MkIso to' from' tf' ft') x y = (x, (from' y))

dep : (a -> Iso b c) -> Iso (a, b) (a, c)
dep f = MkIso to from tf ft
  where
    to : (a, b) -> (a, c)
    to (x, y) = dep_to (f x) x y
    from : (a, c) -> (a, b)
    from (x, y) = dep_from (f x) x y
    tf (x, y) = case (inspect $ f x) of
      (match (MkIso to' from' tf' ft') {eq=fx}) => rewrite fx in
        case (dep_from (MkIso to' from' tf' ft') x y) of
          (x', y') => rewrite fx in
            case (dep_to (MkIso to' from' tf' ft') x (from' y)) of
              (x'', y'') => rewrite (tf' y) in Refl
    ft (x, y) = case (inspect $ f x) of
      (match (MkIso to' from' tf' ft') {eq=fx}) => rewrite fx in
        case (dep_to (MkIso to' from' tf' ft') x y) of
          (x', y') => rewrite fx in
            case (dep_from (MkIso to' from' tf' ft') x (to' y)) of
              (x'', y'') => rewrite (ft' y) in Refl

depVect : (init: Iso a b) ->
        (step: a -> Iso a b) ->
        Iso (Vect n a) (Vect n b)
depVect init step = MkIso (to init) (from init) (tf init) (ft init)
  where
  to : Iso a b -> Vect n a -> Vect n b
  to s [] = []
  to s (x::xs) = appIso s x :: to (step x) xs
  from : Iso a b -> Vect n b -> Vect n a
  from s [] = []
  from s (x::xs) = unappIso s x :: from (step (unappIso s x)) xs
  tf : (step : Iso a b) -> (v : Vect n b) -> to step (from step v) = v
  tf i [] = Refl
  tf i (x::xs) = rewrite (tf (step (unappIso i x)) xs) in case i of
    (MkIso ito ifrom itf ift) => cong (itf x) {f=flip (::) xs}
  ft : (step : Iso a b) -> (v : Vect n a) -> from step (to step v) = v
  ft i [] = Refl
  ft (MkIso ito ifrom itf ift) (x::xs) = rewrite (ift x) in cong (ft (step x) xs) {f=(::) x}

stateVect : (init: Iso a b) ->
          (initS: s) ->
          (step: s -> a -> s) ->
          (gen: s -> Iso a b) ->
          Iso (Vect n a) (Vect n b)
stateVect {s=s} i is step gen = MkIso (to is i) (from is i) (tf is i) (ft is i)
  where
  to : s -> Iso a b -> Vect n a -> Vect n b
  to _ _ [] = []
  to st iso (x::xs) = appIso iso x :: to (step st x) (gen (step st x)) xs
  from : s -> Iso a b -> Vect n b -> Vect n a
  from st iso [] = []
  from st iso (x::xs) = unappIso iso x :: from (step st (unappIso iso x)) (gen (step st (unappIso iso x))) xs
  tf : (st : s) -> (iso : Iso a b) -> (v : Vect n b) -> to st iso (from st iso v) = v
  tf _ _ [] = Refl
  tf st iso (x::xs) = rewrite (tf (step st (unappIso iso x)) (gen (step st (unappIso iso x))) xs) in
    case iso of
      (MkIso ito ifrom itf ift) => cong (itf x) {f=flip (::) xs}
  ft : (st : s) -> (iso : Iso a b) -> (v : Vect n a) -> from st iso (to st iso v) = v
  ft _ _ [] = Refl
  ft st (MkIso ito ifrom itf ift) (x::xs) = rewrite (ift x) in
     cong (ft (step st x) (gen (step st x)) xs) {f=(::) x}






-- examples

xor : Bool -> Bool -> Bool
xor = (/=)

xorTwice : (x,y : Bool) -> xor x (xor x y) = y
xorTwice True True = Refl
xorTwice False False = Refl
xorTwice False True = Refl
xorTwice True False = Refl

test : Iso (Vect n Bool) (Vect n Bool)
test = stateVect idIso False step gen
  where
    idIso = (MkIso id id (\x => Refl) (\x => Refl))
    -- change state when state and value match
    step True True = False
    step False False = True
    step s _ = s
    -- just xor with state
    gen s = MkIso (xor s) (xor s) (xorTwice s) (xorTwice s)

-- λΠ> appIso test [True, True, True, True, True, True, True]
-- [True, True, True, True, True, True, True] : Vect 7 Bool
-- λΠ> appIso test [False, True, False, True, False, True, False]
-- [False, False, False, False, False, False, False] : Vect 7 Bool
-- λΠ> appIso test [False, True, False, False, False, True, False]
-- [False, False, False, True, True, False, False] : Vect 7 Bool

test2 : Iso (Vect n Bool) (Vect n Bool)
test2 = stateVect idIso Z step gen
  where
    idIso = (MkIso id id (\x => Refl) (\x => Refl))
    step Z False = Z
    step (S n) False = n
    step n True = S n
    gen s = MkIso (xor (s == 0)) (xor (s == 0)) (xorTwice (s == 0)) (xorTwice (s == 0))

-- λΠ> appIso test2 [True, True, True, False, False, False, False]
-- [True, True, True, False, False, False, True] : Vect 7 Bool

