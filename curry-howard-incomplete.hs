{-# LANGUAGE TypeOperators #-}
data a :/\: b = a :/\: b
data a :\/: b = L a | R b

data False
type Not a = a -> False

data a :<->: b = Bi { forward :: (a -> b), backward :: (b -> a) }

lhs (a :/\: _) = undefined
rhs (_ :/\: b) = undefined

and_commute :: a :/\: b -> b :/\: a
and_commute (p :/\: q) = undefined

or_commute :: a :\/: b -> b :\/: a
or_commute (L p) = undefined
or_commute (R q) = undefined

and_assoc :: a :/\: (b :/\: c) -> (a :/\: b) :/\: c
and_assoc (p :/\: (q :/\: r)) = undefined

or_assoc :: a :\/: (b :\/: c) -> (a :\/: b) :\/: c
or_assoc (L p) = undefined
or_assoc (R (L q)) = undefined
or_assoc (R (R r)) = undefined

modus_ponens :: a -> (a -> b) -> b
modus_ponens p f = undefined

and_idempotent :: a :/\: a -> a
and_idempotent (p :/\: _) = undefined

or_idempotent :: a :\/: a -> a
or_idempotent (L p) = undefined
or_idempotent (R p) = undefined

and_distributes :: a :/\: (b :\/: c) -> (a :/\: b) :\/: (a :/\: c)
and_distributes (p :/\: L q) = undefined
and_distributes (p :/\: R r) = undefined

or_distributes :: a :\/: (b :/\: c) -> (a :\/: b) :/\: (a :\/: c)
or_distributes (L p)          = undefined
or_distributes (R (q :/\: r)) = undefined

contrapositive :: (a -> b) -> (Not b -> Not a)
contrapositive f g = undefined

demorgan1 :: Not a :\/: Not b -> Not (a :/\: b)
demorgan1 (L f) (p :/\: q) = undefined
demorgan1 (R g) (p :/\: q) = undefined

demorgan2a :: Not a :/\: Not b -> Not (a :\/: b)
demorgan2a (f :/\: g) (L p) = undefined
demorgan2a (f :/\: g) (R q) = undefined

demorgan2b :: Not (a :\/: b) -> Not a :/\: Not b
demorgan2b f = undefined

demorgan2 :: Not a :/\: Not b :<->: Not (a :\/: b)
demorgan2 = undefined

data Scottish    = Scottish
data RedSocks    = RedSocks
data WearKilt    = WearKilt
data Married     = Married
data GoOutSunday = GoOutSunday

no_true_scottsman ::
  (Not Scottish -> RedSocks)          -> -- rule 1
  (WearKilt :\/: Not RedSocks)        -> -- rule 2
  (Married -> Not GoOutSunday)        -> -- rule 3
  (Scottish :<->: GoOutSunday)        -> -- rule 4
  (WearKilt -> Scottish :/\: Married) -> -- rule 5
  (Scottish -> WearKilt)              -> -- rule 6
  False

no_true_scottsman
  rule1
  rule2
  rule3
  rule4
  rule5
  rule6 = let
    lemma1 :: Scottish -> Married
    lemma1 = undefined

    lemma2 :: Scottish -> Not GoOutSunday
    lemma2 = undefined

    lemma3 :: Scottish -> GoOutSunday
    lemma3 = undefined

    lemma4 :: Not Scottish
    lemma4 scottish = undefined

    lemma5 :: RedSocks
    lemma5 = undefined

    lemma6 :: WearKilt :\/: False
    lemma6 = undefined

    lemma7 :: Not WearKilt -> False
    lemma7 f = undefined

    lemma8 :: Not Scottish -> Not WearKilt
    lemma8 f kilt = undefined

    lemma9 :: Not Scottish -> False
    lemma9 = undefined

    in undefined


rule1 :: Not Scottish -> RedSocks
rule2 :: WearKilt :\/: Not RedSocks
rule3 :: Married -> Not GoOutSunday
rule4 :: Scottish :<->: GoOutSunday
rule5 :: WearKilt -> Scottish :/\: Married
rule6 :: Scottish -> WearKilt

rule1 = undefined
rule2 = undefined
rule3 = undefined
rule4 = undefined
rule5 = undefined
rule6 = undefined