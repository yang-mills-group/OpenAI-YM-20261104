import YM.Integration.WilsonPhysicalHistoryPictureHaar
import YM.Integration.WilsonPhysicalHistoryFiscalHaar

/-! The old pupil on its actual admitted sheet can be pushed with the
previous painter still in the integrand. Only the mark constant leaves the
integral. The original fiscal bound purchases the requisite integrability. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGalleryHaar
open Function Finset Lattice Wilson RG Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface MeasureTheory WilsonPhysicalHistoryPictureRestore
open scoped Classical BigOperators

variable {I J V : Type} [Countable I] [Countable J] [DecidableEq V] [Fintype V]
  {G : Gauge} {n c L : Side} {x e κ w b b' z Y Γ K : ℝ} {α : Type*} {A0 : Teller G}
  {Q : ConnectedActivityE6.Target G A0} {horizon : ConnectedActivityE6.Target.Order G w}
  {S : StepData c n} {tube : Pressure.Tube G S} {P : Rep G n} {P' : Rep G c}
  (H : Cash w x κ L Q horizon z tube P) {k : ℕ} (eyes : Eyes H P' e Γ Y K k)
  {R : Census V} {o : V → Site n} (A : Gallery α I o P R)
  (previous : Lamps α J G P.p o R) (weights : V → ℝ)
  (U : Seal (picture A previous) weights b b') (positive : ∀ v, 0 < weights v)
  (slots : HasSlots P.p P.activities) (fits : 2*(b+b') ≤ K)
  (ω : V → ℝ) (pos : ∀ v, 0 < ω v) {a q h : ℝ} (expo : 0 ≤ a)
  (reg : A.E.Paid ω P.p.B (a+2) q) (hard : A.K.Paid ω P.p.B a h)

include H eyes U positive slots fits pos expo reg hard in
theorem charged (t : α) :
    Integrable (retained A previous t) (prior G n) ∧
      ∀ W, (picture A previous).density t W =
        Poly.pass (WilsonPhysicalHistoryGroupedClear.constant A.E t) * retained A previous t W := by
  have whole := (pays (picture A previous) weights U).budget
  have good := WilsonPhysicalHistoryFiscalHaar.original H eyes (picture A previous) weights U
    positive slots t (Travel.fiscal H eyes (picture A previous) weights U positive slots fits t)
  exact ⟨WilsonPhysicalHistoryPictureHaar.retained A previous ω pos expo reg hard t weights positive
    P.p.exponent_pos.le whole good,
    filed A previous ω pos expo reg hard t weights positive P.p.exponent_pos.le whole⟩

end YM.Integration.WilsonPhysicalHistoryGalleryHaar
end

