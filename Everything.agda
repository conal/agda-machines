-- {-# OPTIONS --safe --without-K #-}

{-# OPTIONS --allow-unsolved-metas #-}  -- experiment

module Everything where

open import Categorical

import Ty
import Mealy
import Primitive
import Linearize
import Dot
import Test

import Examples.Add

-- import VecFun
-- import Symbolic

-- -- Experimental modules not used above.
-- import Tinkering.StreamFun
-- import Tinkering.FunFun
-- import Tinkering.SumIso

-- import Tinkering.Reflection.Quote
-- import Tinkering.Reflection.CtoCA
