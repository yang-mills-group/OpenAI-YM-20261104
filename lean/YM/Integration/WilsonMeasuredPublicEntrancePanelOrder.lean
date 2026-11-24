import YM.Integration.WilsonMeasuredPublicEntrancePanel
/-! The physical master pays the same required finite accuracy across all its selected smaller panels. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 4300000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePanelOrder
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
open WilsonReceivedFirstTrace
open Pert.Asymptotics
open Filter WilsonThermometerMixedCollarSubpower
open WilsonThermometerMixedCollarSubpower
open Multi WilsonOriginalAlternativeTrialFunded
open QuadraticLocal.Tint QuadraticLocal.Advent.Oak QuadraticLocal.Earn Filter MeasureTheory
open WilsonAddressedFiniteGuardTrial (printed)
open WilsonMeasuredPublicEntranceSignedEar (weighted)
open Labels Source RG12 Extra.Histories Motion Bandage Trace.Physical.GermGraph
open WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open WilsonThermometerReflectedTrajectory WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale
open WilsonThermometerMarchSource WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open RG05Readout RG05Readout.Native RG05Readout.Address Ac GridApprox.Nil MergeProof MergeProof.Accent
open RG05Readout.Many RG05Readout.Pantry Records WilsonThermometerUnitFilingCoarse
open WilsonAddressedAlignedColumn WilsonReflectedPublicOrientedFaces
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)
variable {G:Gauge} (R:Run G) {V:Type} [Fintype V] [DecidableEq V] (grades:V → ℕ)
local notation "C" => R.family
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "J_" => Stock.census V
local notation "fired_" => WilsonOriginalAlternativeFiniteSource.fired (V:=V)


open WilsonMeasuredPublicEntrancePanel
open WilsonReflectedMixedMasterAxes (Fixed)
open WilsonReflectedOpticalArm (Priced)

/-- A grade and arity cap precedes any choice of the subpanel or source positions. -/
def order (D n requested:ℕ):ℕ:=(n*D+2)*n+(WilsonMeasuredPublicEntranceFixedBill.order requested+1)+2+D

omit [DecidableEq V] in
theorem enough (D n requested:ℕ)(items:Fintype.card V ≤ n)(low:∀v,grades v ≤ D)(v:V):
    accuracy grades requested v ≤ order D n requested:=by
  have cost:(∑v,grades v)≤Fintype.card V*D:=by
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using
      (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _:V=>D) (fun a _=>low a))
  have sum:(∑v,grades v)+2≤n*D+2:=Nat.add_le_add_right (cost.trans (Nat.mul_le_mul_right D items)) 2
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul sum items) (WilsonMeasuredPublicEntranceFixedBill.order requested+1)) 2) (low v)

theorem lower {d j target N per f K small large:ℕ}{first:j≤f}{up:f≤K}{live:K≤N}
    {Y:(C).label d}{M ceiling:ℝ}{F:(C).label d ≃ₗ[ℂ] (C).label d}(mp:0≤M)(le:small≤large)
    (fixed:Fixed R d j target N per f K large first up live Y M ceiling F):
    Fixed R d j target N per f K small first up live Y M ceiling F:=by
  refine ⟨fixed.1,fixed.2.1,?_⟩
  intro s b o
  obtain ⟨A,id,w,branch,turn,placed,cash⟩:=fixed.2.2 s b o
  have one:1≤(H f):=((C).path.levels.fits.delayed f).le
  have price:rent R d M*((H f)^(large+1))⁻¹*((C).S.a f)^d ≤ rent R d M*((H f)^(small+1))⁻¹*((C).S.a f)^d:=by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg ((C).S.a_pos f).le _)
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) mp) (zero_le_one.trans (le_max_left ..)))
    exact inv_anti₀ (pow_pos (zero_lt_one.trans_le one) _) (pow_le_pow_right₀ one (Nat.succ_le_succ le))
  exact ⟨A,id,w,branch,turn,placed,cash.1.trans price,rem_mono cash.2.1 price,
    cash.2.2.1.trans price,cash.2.2.2.trans price⟩

/-- This cap uses the original physical representation at every deposited grade. -/
def capital (D:ℕ)(tuition:ℝ):ℝ:=max 0 ((Finset.univ:Finset (Fin (D+1))).sup' Finset.univ_nonempty
  fun g=>orbitCost ((C).labels.level g.val)*tuition)

theorem placed (D:ℕ)(tuition:ℝ)(g:Fin (D+1)):orbitCost ((C).labels.level g.val)*tuition≤capital R D tuition:=
  (Finset.le_sup' (f:=fun v:Fin (D+1)=>orbitCost ((C).labels.level v.val)*tuition) (Finset.mem_univ g)).trans (le_max_right ..)

end YM.Integration.WilsonMeasuredPublicEntrancePanelOrder
end
