import Common

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

