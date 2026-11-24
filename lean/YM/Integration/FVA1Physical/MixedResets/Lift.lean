import YM.Integration.FVA1Physical.MixedResets.Norm
import YM.QuadraticLocal.Pry
/-! # Arity restoration for joint currency. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG Wilson Marker Ac
open QuadraticLocal QuadraticLocal.Earn
open Push.Corrected Push.AbsoluteSums MeasureTheory
open Integration.LocalComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {V ι X : Type} [Fintype V] [DecidableEq V]
    {I : Marker.Census V} {o : Passport n V} (P : Rep G n)
    (w : V → ℝ) (κ : ℝ) (U : Tint.Incoming o P X ι I) (r : ℝ) (k : ℕ)
namespace Full
variable {P κ U r k} {horizon : ℝ} {a b : ℝ}
omit [Fintype V] in
lemma retake (hk : ∀ i:I.Mode,i.val.card ≤ k) (hw : ∀ i,0<w i) (hh : 1≤r)
    (h : Full P (Stoop.radius w r) κ U horizon a b) : Full P w κ U horizon (r^k*a) (r^k*b) := by
  refine ⟨h.divisor,hw,Stoop.retake w U.old hk hw hh h.regular,?_⟩
  rw [mul_assoc]
  exact Stoop.budget w hk U.hard hw hh h.forced
end Full
end YM.Integration.FVA1Physical.MixedResets
