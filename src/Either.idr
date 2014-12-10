import Common

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
    tf (Right (MkSigma x p)) = Refl
    ft (MkSigma x (Left pa)) = Refl
    ft (MkSigma x (Right pb)) = Refl

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
