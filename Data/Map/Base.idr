module Data.Map.Base


public export

data Map : (k:Type) -> (a:Type) -> Type where
  Bin : Nat -> k -> a -> Map k a -> Map k a -> Map k a
  Tip : Map k a


null : Map k a -> Bool
null (Bin _ _ _ _ _) = False
null Tip             = True


size : Map k a -> Nat
size (Bin s _ _ _ _) = s
size Tip             = 0


lookup : Ord k => k -> Map k a -> Maybe a
lookup _ Tip = Nothing
lookup k (Bin _ kx x l r) =
  case compare k kx of
    LT => lookup k l
    GT => lookup k r
    EQ => Just x


member : Ord k => k -> Map k a -> Bool
member k = isJust . lookup k

notMember : Ord k => k -> Map k a -> Bool
notMember k = not . member k


lookupLT : Ord k => k -> Map k a -> Maybe (k,a)
lookupLT = goNothing
  where
    goNothing : Ord k => k -> Map k a -> Maybe (k,a)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
        if k <= kx
        then goNothing k l
        else goJust k kx x r
      where
        goJust : {k:Type} -> Ord k => k -> k -> a -> Map k a -> Maybe (k,a)
        goJust _ kx' x' Tip              = Just (kx', x')
        goJust k kx' x' (Bin _ kx x l r) =
          if k <= kx
          then goJust k kx' x' l
          else goJust k kx x r


lookupGT : Ord k => k -> Map k a -> Maybe (k,a)
lookupGT = goNothing
  where
    goNothing : Ord k => k -> Map k a -> Maybe (k,a)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
        if k < kx
        then goJust k kx x l
        else goNothing k r
      where
        goJust : {k:Type} -> Ord k => k -> k -> a -> Map k a -> Maybe (k,a)
        goJust _ kx' x' Tip              = Just (kx', x')
        goJust k kx' x' (Bin _ kx x l r) =
          if k < kx
          then goJust k kx x l
          else goJust k kx' x' r


lookupLE : Ord k => k -> Map k a -> Maybe (k,a)
lookupLE = goNothing
  where
    goNothing : Ord k => k -> Map k a -> Maybe (k,a)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case compare k kx of
        LT => goNothing k l
        EQ => Just (kx, x)
        GT => goJust k kx x r
      where
        goJust : {k:Type} -> Ord k => k -> k -> a -> Map k a -> Maybe (k,a)
        goJust _ kx' x' Tip              = Just (kx', x')
        goJust k kx' x' (Bin _ kx x l r) =
          case compare k kx of
            LT => goJust k kx' x' l
            EQ => Just (kx, x)
            GT => goJust k kx x r


lookupGE : Ord k => k -> Map k a -> Maybe (k,a)
lookupGE = goNothing
  where
    goNothing : Ord k => k -> Map k a -> Maybe (k,a)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case compare k kx of
        LT => goJust k kx x l
        EQ => Just (kx, x)
        GT => goNothing k r
      where
        goJust : {k:Type} -> Ord k => k -> k -> a -> Map k a -> Maybe (k,a)
        goJust _ kx' x' Tip              = Just (kx', x')
        goJust k kx' x' (Bin _ kx x l r) =
          case compare k kx of
            LT => goJust k kx x l
            EQ => Just (kx, x)
            GT => goJust k kx' x' r



empty : Map k a
empty = Tip

singleton : k -> a -> Map k a
singleton k x = Bin 1 k x Tip Tip


ratio : Nat
ratio = 2

delta : Nat
delta = 3

balanceL : k -> a -> Map k a -> Map k a -> Map k a
balanceL k x l r = case r of
  Tip => case l of
           Tip                                      => singleton k x
           (Bin _  _   _  Tip Tip)                  => Bin 2 k x l Tip
           (Bin _  lk  lx Tip (Bin _ lrk lrx _ _))  => Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
           (Bin _  lk  lx ll@(Bin _   _ _ _ _) Tip) => Bin 3 lk  lx  ll                    (Bin 1 k x Tip Tip)
           (Bin ls lk  lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr)) =>
              if lrs < ratio * lls
              then Bin (1 + ls) lk  lx
                     ll
                     (Bin (1 + lrs)            k  x  lr  Tip)
              else Bin (1 + ls) lrk lrx
                     (Bin (1 + lls + size lrl) lk lx ll  lrl)
                     (Bin (1 + size lrr)       k  x  lrr Tip)
  (Bin rs _ _ _ _) => case l of
                        Tip => Bin (1 + rs) k x Tip r
                        (Bin ls lk lx ll lr) =>
                          if ls > delta*rs
                          then case (ll, lr) of
                                 (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr) =>
                                    if lrs < ratio*lls
                                    then Bin (1 + ls + rs) lk lx
                                           ll
                                           (Bin (1 + rs + lrs) k x lr r)
                                    else Bin (1 + ls + rs) lrk lrx
                                           (Bin (1 + lls + size lrl) lk lx ll lrl)
                                           (Bin (1 + rs  + size lrr) k x lrr r)
                                 (_, _) => believe_me  "Failure in Data.Map.balanceL"
                          else Bin (1 + ls + rs) k x l r



balanceR : k -> a -> Map k a -> Map k a -> Map k a
balanceR k x l r = case l of
  Tip => case r of
           Tip => Bin 1 k x Tip Tip
           (Bin _ _ _ Tip Tip)                   => Bin 2 k x Tip r
           (Bin _ rk rx Tip rr@(Bin _ _ _ _ _))  => Bin 3 rk rx (Bin 1 k x Tip Tip) rr
           (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) => Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
           (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =>
             if rls < ratio*rrs
             then Bin (1 + rs) rk  rx
                    (Bin (1 + rls) k x Tip rl)
                    rr
             else Bin (1 + rs) rlk rlx
                    (Bin (1 + size rll) k x Tip rll)
                    (Bin (1 + rrs + size rlr) rk rx rlr rr)

  (Bin ls _ _ _ _) => case r of
     Tip => Bin (1 + ls) k x l Tip
     (Bin rs rk rx rl rr) =>
        if rs > delta*ls
        then case (rl, rr) of
               (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _) =>
                  if rls < ratio * rrs
                  then Bin (1 + ls + rs) rk rx
                         (Bin (1 + ls + rls) k x l rl)
                         rr
                  else Bin (1 + ls + rs) rlk rlx
                         (Bin (1 + ls  + size rll) k x l rll)
                         (Bin (1 + rrs + size rlr) rk rx rlr rr)
               (_, _) => believe_me  "Failure in Data.Map.balanceR"
        else Bin (1 + ls + rs) k x l r


insert : Ord k => k -> a -> Map k a -> Map k a
insert kx x Tip = singleton kx x
insert kx x (Bin s ky y l r) =
  case compare kx ky of
    LT => balanceL ky y (insert kx x l) r
    GT => balanceR ky y l (insert kx x r)
    EQ => Bin s ky x l r

insertR : Ord k => k -> a -> Map k a -> Map k a
insertR kx x Tip = singleton kx x
insertR kx x t@(Bin _ ky y l r) =
  case compare kx ky of
    LT => balanceL ky y (insertR kx x l) r
    GT => balanceR ky y l (insertR kx x r)
    EQ => t

insertWithKey : Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWithKey _ kx x Tip = singleton kx x
insertWithKey f kx x (Bin sy ky y l r) =
  case compare kx ky of
    LT => balanceL ky y (insertWithKey f kx x l) r
    GT => balanceR ky y l (insertWithKey f kx x r)
    EQ => Bin sy kx (f kx x y) l r

insertWith : Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith f = insertWithKey (\_, x, y => f x y)

insertLookupWithKey : Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a, Map k a)
insertLookupWithKey _ kx x Tip = (Nothing, singleton kx x)
insertLookupWithKey f kx x (Bin sy ky y l r) =
  case compare kx ky of
    LT => let (found, ls) = insertLookupWithKey f kx x l
          in  (found, balanceL ky y ls r)
    GT => let (found, rs) = insertLookupWithKey f kx x r
          in  (found, balanceR ky y l rs)



deleteFindMin : Map k a -> ((k,a),Map k a)
deleteFindMin t = case t of
  Bin _ k x Tip r => ((k,x),r)
  Bin _ k x l r => let (km,l') = deleteFindMin l
                   in ( km
                      , balanceR k x l' r
                      )
  Tip => ( believe_me  "Map.deleteFindMin: can not return the minimal element of an empty map"
         , Tip
         )


deleteFindMax : Map k a -> ((k,a),Map k a)
deleteFindMax t = case t of
  Bin _ k x l Tip => ((k,x),l)
  Bin _ k x l r => let (km,r') = deleteFindMax r
                   in ( km
                      , balanceL k x l r'
                      )
  Tip => ( believe_me "Map.deleteFindMax: can not return the maximal element of an empty map"
         , Tip
         )


glue : Map k a -> Map k a -> Map k a
glue Tip r = r
glue l Tip = l
glue l r =
  if size l > size r
  then let ((km,m),l') = deleteFindMax l
       in  balanceR km m l' r
  else let ((km,m),r') = deleteFindMin r
       in balanceL km m l r'


delete : Ord k => k -> Map k a -> Map k a
delete _ Tip = Tip
delete k (Bin s kx x l r) =
  case compare k kx of
    LT => balanceL kx x (delete k l) r
    GT => balanceR kx x l (delete k r)
    EQ => glue l r


insertMax : k -> a -> Map k a -> Map k a
insertMax kx x t = case t of
  Tip => singleton kx x
  Bin _ ky y l r => balanceR ky y l (insertMax kx x r)

insertMin : k -> a -> Map k a -> Map k a
insertMin kx x t = case t of
  Tip => singleton kx x
  Bin _ ky y l r => balanceL ky y (insertMin kx x l) r

bin : k -> a -> Map k a -> Map k a -> Map k a
bin k x l r = Bin (size l + size r + 1) k x l r


link : k -> a -> Map k a -> Map k a -> Map k a
link kx x Tip r = insertMin kx x r
link kx x l Tip = insertMax kx x l
link kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz) =
  if delta * sizeL < sizeR
  then balanceL kz z (link kx x l lz) rz
  else if delta * sizeR < sizeL
       then balanceR ky y ly (link kx x ry r)
       else bin kx x l r



filterGt : Ord k => Maybe k -> Map k v -> Map k v
filterGt Nothing  t = t
filterGt (Just b) t = filter' b t
  where
    filter' _   Tip = Tip
    filter' b' (Bin _ kx x l r) =
      case compare b' kx of
        LT => link kx x (filter' b' l) r
        EQ => r
        GT => filter' b' r


filterLt : Ord k => Maybe k -> Map k v -> Map k v
filterLt Nothing  t = t
filterLt (Just b) t = filter' b t
  where
    filter' _   Tip = Tip
    filter' b' (Bin _ kx x l r) =
      case compare kx b' of
        LT => link kx x l (filter' b' r)
        EQ => l
        GT => filter' b' l


trim : Ord k => Maybe k -> Maybe k -> Map k a -> Map k a
trim Nothing   Nothing t = t
trim (Just lk) Nothing t = greater lk t
  where
    greater lo t'@(Bin _ k _ _ r) =
      if k <= lo
      then greater lo r
      else t'
    greater _ t' = t'
trim Nothing (Just hk) t = lesser hk t
  where
    lesser hi t'@(Bin _ k _ l _) =
      if k >= hi
      then lesser  hi l
      else t'
    lesser  _  t' = t'
trim (Just lk) (Just hk) t = middle lk hk t
  where
    middle lo hi t'@(Bin _ k _ l r) =
      if k <= lo
      then middle lo hi r
      else if k >= hi
           then middle lo hi l
           else t'
    middle _  _  t' = t'



trimLookupLo : Ord k => k -> Maybe k -> Map k a -> (Maybe a, Map k a)
trimLookupLo lk0 mhk0 t0 = go lk0 mhk0 t0
  where
    go lk Nothing t = greater lk t
      where greater : Ord k => k -> Map k a -> (Maybe a, Map k a)
            greater lo t'@(Bin _ kx x l r) = case compare lo kx of
                LT => (lookup lo l, t')
                EQ => (Just x, r)
                GT => greater lo r
            greater _ Tip = (Nothing, Tip)
    go lk (Just hk) t = middle lk hk t
      where
        lesser : Ord k => k -> Map k a -> Map k a
        lesser hi t'@(Bin _ k _ l _) =
          if k >= hi
          then lesser hi l
          else t'
        lesser _ t' = t'

        middle : Ord k => k -> k -> Map k a -> (Maybe a, Map k a)
        middle lo hi t'@(Bin _ kx x l r) = case compare lo kx of
          LT => if kx < hi
                then (lookup lo l, t')
                else middle lo hi l
          EQ => (Just x, lesser hi r)
          GT => middle lo hi r
        middle _ _ Tip = (Nothing, Tip)




merge : Map k a -> Map k a -> Map k a
merge Tip r   = r
merge l Tip   = l
merge l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry) =
  if delta * sizeL < sizeR
  then balanceL ky y (merge l ly) ry
  else if delta * sizeR < sizeL
       then balanceR kx x lx (merge rx r)
       else glue l r


mergeWithKey : {k:Type} -> Ord k => (k -> a -> b -> Maybe c)
                     -> (Map k a -> Map k c)
                     -> (Map k b -> Map k c)
                     -> Map k a -> Map k b -> Map k c
mergeWithKey f g1 g2 = go
  where
    hedgeMerge : Maybe k -> Maybe k -> Map k a -> Map k b -> Map k c
    hedgeMerge _   _   t1  Tip = g1 t1
    hedgeMerge blo bhi Tip (Bin _ kx x l r) = g2 $ link kx x (filterGt blo l) (filterLt bhi r)
    hedgeMerge blo bhi (Bin _ kx x l r) t2 =
      let l' = hedgeMerge blo bmi l (trim blo bmi t2)
          (found, trim_t2) = trimLookupLo kx bhi t2
          r' = hedgeMerge bmi bhi r trim_t2
      in case found of
        Nothing => case g1 (singleton kx x) of
                     Tip => merge l' r'
                     (Bin _ _ x' Tip Tip) => link kx x' l' r'
                     _ => believe_me "mergeWithKey: Given function only1 does not fulfil required conditions (see documentation)"
        Just x2 => case f kx x x2 of
                     Nothing => merge l' r'
                     Just x' => link kx x' l' r'
      where bmi = Just kx

    go Tip t2 = g2 t2
    go t1 Tip = g1 t1
    go t1 t2 = hedgeMerge Nothing Nothing t1 t2

