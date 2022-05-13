module Game.Morphs

import Game.Core

%default total

dist01 : {0 m : Game} -> Iso (sequo I m) I
dist01 {m=Gam f} = Bsm (Sim id (\x => void x))
                       (Sim id (\x => void x))

dist02 : {0 p : Game} -> Iso (lolli p I) I
dist02 {p=Gam f} = Bsm (Sim id (\x => void x))
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
