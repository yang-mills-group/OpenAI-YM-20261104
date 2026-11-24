import YM.SchemeConversionRG11.FirstW.Lien.Key
/-! Interpolate polynomial weights of the *lattice* correction; no DR hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {i j k : ℕ}
lemma lamp (p:Rhythm G) (h:ToneR p k) (i j:ℕ) (hij:i+j≤k) (m:i≤4)(r:j≤4): ∀ x:Nu G i,∀ y:Nu G j, (quietly x.val ∨ quietly y.val) → patchR p i j m r x y=0 := by
 intro x y hk
 rcases hk with hk|hk
 · rw [pin]; have hx : (boards i m x).val∈cabin G i:=by rw [boards_val]; exact x.property -- split
   have hy : (boards j r y).val∈cabin G j:=by rw [boards_val]; exact y.property
   exact (h _ _).2 i j hij hx hy (by rw [boards_val]; exact hk)
 rw [pin,(h (boards i m x) _).1]
 apply (h (boards j r y) (boards i m x)).2 j i (by omega)
 · rw [boards_val]; exact y.property
 · rw [boards_val]; exact x.property
 rw [boards_val]; exact hk
-- ordered with no half-card conventions hidden
def ripple (G : Gauge) (p : Rhythm G) (q : Reel G) (k : ℕ) := ∀ (i j:ℕ), i+j≤k → ∀ a b:la G,a.val∈cabin G i → b.val∈cabin G j → p a b=chord a.val b.val q.val
end YM.RG11.FirstW
