import YM.Integration.WilsonPhysicalHistoryRootFiscal

/-! Absolute integrability of the complete enrolled pupil under the original
fine Haar law. The ordinary vote on the three-test sheet pays its own
original expansion. The finite marker board supplies the chorus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFiscalHaar
open Function Finset Lattice Wilson RG Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface GridRenewal.Rain MeasureTheory WilsonPhysicalHistoryRootFiscal
open scoped Classical BigOperators

variable {I V : Type} [Countable I] [DecidableEq V] [Fintype V] {G : Gauge} {n c L : Side}
  {x e κ w b b' z Y Γ K : ℝ} {α : Type*} {A0 : Teller G}
  {Q : ConnectedActivityE6.Target G A0} {horizon : ConnectedActivityE6.Target.Order G w}
  {S : StepData c n} {tube : Pressure.Tube G S} {P : Rep G n} {P' : Rep G c}
  (H : Cash w x κ L Q horizon z tube P) {k : ℕ} (eyes : Eyes H P' e Γ Y K k)
  {R : Census V} {o : V → Site n} (A : Gallery α I o P R) (weights : V → ℝ)
  (U : Seal A weights b b') (positive : ∀ v, 0 < weights v) (slots : HasSlots P.p P.activities)

theorem original (t : α) (ordinary : Motto (brand (invoice A weights U positive slots) t)
    (fun _ => 1) 0 H P.p.supportExponent K Y (Eyes.sight eyes)) :
    Integrable (A.density t) (prior G n) := by
  have chorus := choir A weights positive (Fintype.card V) (fun i => Finset.card_le_univ i.val)
  have representation := fun W => Trigger.same A S weights positive slots U.supE U.crown
    (sighting A weights U) U.looks t W H ordinary chorus (pays A weights U).budget P.p.exponent_pos.le
  have paid := Encore.oil (brand (invoice A weights U positive slots) t) Set.univ (fun _ => 1)
    (axis A weights) H chorus ordinary
  rw [funext representation]
  let mult : Poly R →ₗ[ℂ] Poly R := Algebra.lmul ℂ (Poly R) (cyclone (globes A t))
  exact ((LinearMap.toContinuousLinearMap mult).restrictScalars ℝ).integrable_comp paid

end YM.Integration.WilsonPhysicalHistoryFiscalHaar
end

