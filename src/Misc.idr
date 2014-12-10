import Common

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
