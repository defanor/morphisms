import Control.Isomorphism

%default total

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

data Inspect : a -> Type where
  wi : {A : Type} -> (x : A) -> (y : A) -> (eq: x = y) -> Inspect x

inspect : {A : Type} -> (x : A) -> Inspect x
inspect x = wi x _ Refl

match : {A : Type} -> {x : A} -> (y : A) -> {eq : x = y} -> Inspect x
match y {eq} = wi _ y eq


appIso : Iso a b -> a -> b
appIso (MkIso to _ _ _) x = to x

unappIso : Iso a b -> b -> a
unappIso (MkIso _ from _ _) x = from x

