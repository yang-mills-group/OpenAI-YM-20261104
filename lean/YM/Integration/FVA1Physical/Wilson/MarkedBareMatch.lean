import YM.Integration.FVA1Physical.Wilson.BareCoefficients
import YM.Integration.FVA1Physical.Wilson.BareAction
import YM.Integration.MSMatch.SourceTop

/-! Coefficientwise identification of the normalized `RG02.Bulk.Fk` top-step
coefficients with the FVA2 physical `Spool.lens` prescription. Both sides
use the same family, oriented stencils, source positions, coarse field, Wilson
action, block kernel and entire conditional vacuum. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Wilson

open Filter Function MeasureTheory
open YM.Lattice YM.RG YM.Wilson YM.Tree YM.Precision YM.Exterior YM.Marker
open YM.Comparison.RG02 YM.FVA2.CityHistory YM.FormalOPE.RG10.InversionTop
open YM.RGComparison.Core16 YM.RGComparison.Core16.Spool
open YM.RGComparison.Core16.Parcel YM.RGComparison.Core16.Parcel.Oven
open YM.PertExtension.Series.Tested
open scoped Classical BigOperators

variable {G : Gauge} {C : Family G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {d m p : ℕ} (R : Census ι) (U : ι → Stamp.Reservation C (C.side (m+1) p) d)
    (hC : C.Makes) (hs : ∀ i, Bid.pop (C.localSection i))
local notation "St" => C.path.levels.clock.op m p

/-- One physical lamp for each marker actually present, even when distinct
markers share a field or a position. -/
def modeLamp (s : R.Mode) (j : s.val) : Lamp G :=
  investment (hC.sections (U j).height) (hs (U j).height) (U j).leg

def modeSite (s : R.Mode) (j : s.val) : Site (C.side (m+1) p) := (U j).anchor

local notation "J" => modeLamp R U hC hs
local notation "y" => modeSite R U

omit [Fintype ι] in
theorem joint_stencils (s : R.Mode) (g : ℝ) (A : Config G (C.side (m+1) p)) :
    (∏ i ∈ s.val, (g ^ MSMatch.SourceTop.grade U i)⁻¹ • MSMatch.SourceTop.field U i A) =
      g⁻¹ ^ power (J s) • column (J s) (y s) A := by
  simp only [Complex.real_smul, ← inv_pow, Complex.ofReal_pow, Complex.ofReal_inv, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  change (g⁻¹ : ℂ) ^ (∑ i ∈ s.val, MSMatch.SourceTop.grade U i) *
    (∏ i ∈ s.val, MSMatch.SourceTop.field U i A) =
      (g⁻¹ : ℂ) ^ (∑ j : s.val, MSMatch.SourceTop.grade U j) *
        (∏ j : s.val, MSMatch.SourceTop.field U j A)
  rw [Finset.sum_coe_sort, Finset.prod_coe_sort s.val (fun i => MSMatch.SourceTop.field U i A)]

variable (u : Pins G (C.side m p))

private lemma ray (g : ℝ) : Integral.sample g (axesP G (C.side m p) u) = slice u g := by
  unfold Integral.sample
  rw [← (axesP G (C.side m p)).map_smul, direct_link]
  rfl

omit [Fintype ι] in
/-- The actual source-bank ratio and the physical comparison readout at the
same coupling, before any expansion or removal of a regulator. -/
theorem sourceRatio_eq_reads (s : R.Mode) (g : ℝ) :
    (MSMatch.SourceTop.torusVacuum (C := C) m p (axesP G _ u) g)⁻¹ •
      MSMatch.SourceTop.torusFull m p U (axesP G _ u) s.val g = reads (J s) St u (y s) g := by
  let z := g⁻¹ ^ power (J s)
  let β := g⁻¹ ^ 2
  let A := fun X : Config G (C.side (m+1) p) => bare β X • column (J s) (y s) X
  have ht : Integral.temperature g = β := (inv_pow g 2).symm
  have he (X : Config G (C.side (m+1) p)) :
      (bare β X : ℂ) * (∏ i ∈ s.val, (g ^ MSMatch.SourceTop.grade U i)⁻¹ •
        MSMatch.SourceTop.field U i X) = z • A X := by
    rw [joint_stencils R U hC hs s g X]
    unfold A z
    simp only [Complex.real_smul, mul_left_comm]
  unfold MSMatch.SourceTop.torusVacuum MSMatch.SourceTop.torusFull reads spinVac survey
  rw [ray u g, ht]
  simp_rw [he]
  change ((St).push β (bare β) (slice u g))⁻¹ • (St).push β (z • A) (slice u g) =
    z • (((St).push β (bare β) (slice u g))⁻¹ • (St).push β A (slice u g))
  have hmul : (St).push β (z • A) = z • (St).push β A := by
    funext X
    simp only [StepData.push, Pi.smul_apply, smul_comm (_ : ℝ) z, MeasureTheory.integral_smul]
  rw [hmul, Pi.smul_apply, smul_comm]

variable (L : Bulk.Chain C.path)

/-- No equality of coefficient systems or of integrals is assumed. At every
admitted finite marker mode and every order within the requested truncation,
uniqueness of the common physical expansion identifies the two coefficients. -/
theorem normalized_coefficients (F : Forest (St).ratio) (t : (St).Choices) (s : R.Mode)
    {P : Oven (St).patch} {X : P.Form G}
    {Z : ChartRatio G} (H : P.Offers X (St).kernel) (h : Bid.Larger (G := G) St)
    (hu : ∀ i, ‖u i‖ ≤ X.Q) (hZ : LocalRatio Z) {k r : ℕ} (hk : k ≤ r) :
    (MSMatch.SourceTop.datum R m p U F t (axesP G _ u)).ordinaryCoefficient L r k s =
      rank (J s) St F X Z u (y s) k := by
  have hj : Laplace.Trial (rank (J s) St F X Z u (y s)) (reads (J s) St u (y s)) r := by
    let B : Lumen.Stage := ⟨1, 0, le_rfl⟩
    obtain ⟨B', a, _, ha, H'⟩ := every (J s) H B r hZ
    have hp := H' (C.side m p) (C.side (m+1) p) (St).sizes h F u (y s) hu
    refine ⟨a, ha, ?_⟩
    filter_upwards [eventually_small (Forge.dollar_pos B'.L)] with g hg
    exact (hp.cost g hg.1 hg.2.le).trans_eq (mul_comm _ _)
  have he := Laplace.trial_congr (Eventually.of_forall fun g => (sourceRatio_eq_reads R U hC hs u s g).symm) hj
  exact (MSMatch.SourceTop.source_step_unique L R m p U F t (axesP G _ u) hC hs s _ he hk).symm

end YM.Integration.FVA1Physical.Wilson

