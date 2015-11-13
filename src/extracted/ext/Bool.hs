module Bool where

import qualified Prelude
import qualified Logic


data Coq_reflect =
   ReflectT
 | ReflectF

iff_reflect :: Prelude.Bool -> Coq_reflect
iff_reflect b =
  case b of {
   Prelude.True -> Logic.and_rec (\_ _ -> ReflectT);
   Prelude.False -> Logic.and_rec (\_ _ -> ReflectF)}

