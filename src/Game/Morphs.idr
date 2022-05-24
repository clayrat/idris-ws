module Game.Morphs

import Game.Core

%default total

dist01 : {0 g : Game} -> Iso (sequo I g) I
dist01 {g=Gam f} = Bsm (Sim id (\x => void x))
                       (Sim id (\x => void x))

dist02 : {0 g : Game} -> Iso (lolli g I) I
dist02 {g=Gam f} = Bsm (Sim id (\x => void x))
                       (Sim id (\x => void x))

mutual
  unitLolli : {0 g : Game} -> Iso (lolli I g) g
  unitLolli {g=Gam f} = Bsm (Sim id (\m => wk1 $ unitTen {g=f m}))
                            (Sim id (\m => wk2 $ unitTen {g=f m}))

  unitTen : {0 g : Game} -> Iso (ten g I) g
  unitTen {g=Gam f} = Bsm (Sim (\case Left m => m
                                      Right v => void v)
                               (\case Left m => wk1 $ unitLolli {g=f m}
                                      Right v => void v))
                          (Sim Left (\m => wk2 $ unitLolli {g=f m}))

unitSequo : {0 g : Game} -> Iso (sequo g I) g
unitSequo {g=Gam f} = Bsm (Sim id (\i => wk1 $ unitLolli {g=f i}))
                          (Sim id (\i => wk2 $ unitLolli {g=f i}))

symTen : {0 a, b : Game} -> Iso (ten a b) (ten b a)
symTen {a=Gam f} {b=Gam g} = Bsm (Sim (copair Right Left) (copair (\x => morId) (\x => morId)))
                                 (Sim (copair Right Left) (copair (\x => morId) (\x => morId)))

dist10 : {0 g : Game} -> Iso (ten I g) g
dist10 = isoTrans symTen unitTen

dec1 : {0 a, b : Game} -> Iso (ten a b) (prod (sequo a b) (sequo b a))
dec1 {a=Gam f} {b=Gam g} = Bsm (Sim id (\x => morId))
                               (Sim id (\x => morId))

dist1 : {0 a, b, c : Game} -> Iso (sequo (prod a b) c) (prod (sequo a c) (sequo b c))
dist1 {a=Gam f} {b=Gam g} {c=Gam h} = Bsm (Sim id (copair (\x => morId) (\x => morId)))
                                          (Sim id (copair (\x => morId) (\x => morId)))
