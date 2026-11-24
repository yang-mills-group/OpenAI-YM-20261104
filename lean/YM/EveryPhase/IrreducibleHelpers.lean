import YM.Paley.Line

/-!
Restore the original closed upper-half-plane lemma removed during pruning.
Its statement and proof are copied verbatim
from YM/Paley/Line.lean:18.
-/
set_option autoImplicit false
namespace YM.Paley
open Complex

lemma highC : IsClosed high := isClosed_le continuous_const continuous_im

end YM.Paley
