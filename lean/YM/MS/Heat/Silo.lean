import Mathlib.Order.Filter.Basic
import YM.MS.KoszulAllocate

set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Koszul
variable {I : Type}

lemma gathers {A R:Type} [CommRing R] {s:Filter I}(w:Legs A)(p:Sector A)(U:I→ Shared A R)(V:Shared A R)(H:∀ i j, Split i j w→∀ᶠ u in s,U u i j=V i j): ∀ᶠ u in s, scatter p w (U u)=scatter p w V:= by
   induction w generalizing U V with
   | nil=> exact H [] [] .nil
   | cons a w ih=> refine ih _ _ (fun i j h=>?_); filter_upwards [H _ _ h.left,H _ _ h.right] with v hv hq; rw [hv,hq]
end YM.MS.Heat
