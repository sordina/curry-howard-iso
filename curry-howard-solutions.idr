module curry_howard_solutions

-- Note: Spoilers! Solutions Included!

%default total

infixl 4 /\
infixl 4 :/\

data (:/\) : Type -> Type -> Type where
      (/\) : {a : Type} -> {b : Type} -> a -> b -> a :/\ b

infixl 3 :\/

data (:\/) : Type -> Type -> Type where
     L     : {a : Type} -> {b : Type} -> a -> a :\/ b
     R     : {a : Type} -> {b : Type} -> b -> a :\/ b

-- data Void
-- Not : Type
-- Not a = a -> Void

infixr 2 :<->

record (:<->) : Type -> Type -> Type where
      (<->)   :  {a : Type}
              -> {b : Type}
              -> (forward  : a -> b)
              -> (backward : b -> a)
              -> a :<-> b

lhs : {a : Type} -> {b : Type} -> a :/\ b -> a
lhs (x /\ _) = x

rhs : {a : Type} -> {b : Type} -> a :/\ b -> b
rhs (_ /\ y) = y

and_commutes : {a : Type} -> {b : Type} -> a :/\ b -> b :/\ a
and_commutes (x /\ y) = y /\ x

and_associates : (a :/\ b) :/\ c -> a :/\ (b :/\ c)
and_associates ((x /\ z) /\ y) = x /\ (z /\ y)

or_commutes : a :\/ b-> b :\/ a
or_commutes (L x) = R x
or_commutes (R x) = L x

or_associates : (a :\/ b) :\/ c -> a :\/ (b :\/ c)
or_associates (L (L x)) = L x
or_associates (L (R x)) = R (L x)
or_associates    (R x)  = R (R x)

modus_ponens : a -> (a -> b) -> b
modus_ponens v f = f v

and_indempotent : a :/\ b -> a
and_indempotent = lhs

or_indempotent : a :\/ a -> a
or_indempotent (L x) = x
or_indempotent (R x) = x

and_distributes : a :/\ (b :\/ c) -> (a :/\ b) :\/ (a :/\ c)
and_distributes (x /\ (L y)) = L (x /\ y)
and_distributes (x /\ (R y)) = R (x /\ y)

or_distributes : a :\/ (b :/\ c) -> (a :\/ b) :/\ (a :\/ c)
or_distributes (L x)        = L x /\ L x
or_distributes (R (x /\ y)) = R x /\ R y

contrapositive : (a -> b) -> (Not b -> Not a)
contrapositive f pbf = pbf . f

demorgan_1 : Not a :\/ Not b -> Not (a :/\ b)
demorgan_1 (L x) = x . lhs
demorgan_1 (R x) = x . rhs

demorgan_2a : Not a :/\ Not b -> Not (a :\/ b)
demorgan_2a (x /\ y) (L f) = x f
demorgan_2a (x /\ y) (R f) = y f

demorgan_2b : Not (a :\/ b) -> Not a :/\ Not b
demorgan_2b f = f . L /\ f . R

demorgan2 : Not a :/\ Not b :<-> Not (a :\/ b)
demorgan2 = demorgan_2a <-> demorgan_2b

data Scottish    : Type
data RedSocks    : Type
data WearKilt    : Type
data Married     : Type
data GoOutSunday : Type

no_true_scottsman :
  (Not Scottish -> RedSocks)             -> -- rule 1
  (WearKilt    :\/ Not RedSocks)         -> -- rule 2
  (Married      -> Not GoOutSunday)      -> -- rule 3
  (Scottish   :<-> GoOutSunday)          -> -- rule 4
  (WearKilt     -> Scottish :/\ Married) -> -- rule 5
  (Scottish     -> WearKilt)             -> -- rule 6
  Void

no_true_scottsman
        rule1 rule2 rule3 rule4 rule5 rule6
        
        = lemma9 lemma4
        
        where
        
        lemma1 : Scottish -> Married
        lemma1 = rhs . rule5 . rule6
        
        lemma2 : Scottish -> Not GoOutSunday
        lemma2 = rule3 . lemma1
        
        lemma3 : Scottish -> GoOutSunday
        lemma3 = forward rule4
        
        lemma4 : Not Scottish
        lemma4 scottish = modus_ponens (lemma3 scottish) (lemma2 scottish)
        
        lemma5 : RedSocks
        lemma5 = rule1 lemma4
        
        lemma6 : WearKilt :\/ Void
        lemma6 = case rule2 of (L wearing_a_kilt) => L wearing_a_kilt
                               (R not_redsocks)   => R (not_redsocks lemma5)
        
        lemma7 : Not (Not WearKilt)
        lemma7 f = case lemma6 of (L wearingKilt) => f wearingKilt
                                  (R voidish)     => voidish
        
        lemma8 : Not Scottish -> Not WearKilt
        lemma8 f wearing_a_kilt = f (lhs (rule5 wearing_a_kilt))
        
        lemma9 : Not (Not Scottish)
        lemma9 = lemma7 . lemma8
