import YM.Integration.WilsonAddressedPostFarMasks

/-! The native numerical flag indicator on one actual original ball.
The quiet gas alone supplies the failed owner on every nonzero field. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedFlagIndicator
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Push.Corrected
open Source Labels Planned.GuardedAtom Extra.Histories WilsonCenteredCaptureRegularAtoms WilsonCenteredLampCapture
open WilsonCenteredFiledAtoms WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftRoster
open WilsonRootedKioskOccupiedSlip Comparison.RG02.Cumulants WilsonCenteredCaptureSlots WilsonCenteredFailedHalo
open WilsonMeasuredCoefficientTransport WilsonFullFaceSignedMasks WilsonCenteredHardMount WilsonCenteredHardAnswers WilsonCenteredAbsoluteHard
open WilsonReceivedQuietCrownOwner
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} (P : Rep G n)
def badge (t : ℝ) (Z : Support n) (U : Config G n) : ℂ := if Healthy t Z U then 0 else 1

theorem value (t : ℝ) (Z : Support n) (U : Config G n) :
    badge t Z U = if (flags t U ∩ Z).Nonempty then 1 else 0 := by
  by_cases h : Disjoint Z (flags t U)
  · have e : flags t U ∩ Z = ∅ := disjoint_iff_inter_eq_empty.mp h.symm
    simp [badge,Healthy,e,h]
  · have e : (flags t U ∩ Z).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (fun eq => h (disjoint_iff_inter_eq_empty.mpr (by rwa [inter_comm])))
    simp [badge,Healthy,e,h]

theorem attaches (t : ℝ) (Z : Support n) : Attaches t Z (badge (G:=G) t Z) where
  sites U W _ flags := by
    have same : Healthy t Z U ↔ Healthy t Z W := by simp only [Healthy,disjoint_iff_inter_eq_empty,flags]
    by_cases h : Healthy t Z U
    · simp [badge,h,same.mp h]
    · simp [badge,h,mt same.mpr h]
  symmetry g U := by
    have same : Healthy t Z (gauge g U) ↔ Healthy t Z U := by rw [Healthy,Healthy,gauge_flags]
    by_cases h : Healthy t Z U
    · simp [badge,h,same.mpr h]
    · simp [badge,h,mt same.mp h]
  borel := Measurable.ite (healthy_closed t Z).measurableSet measurable_const measurable_const
  healthy_zero U ok := if_pos ok

theorem original (K : Guard.Keeper P.p P.activities) (Y : Hol G) (y : Site n) {κ v : ℝ}
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (law : P.activities.ForcedFamily P.p) (quiet : P.activities.KBound P.p v) :
    let Z := halo P.p.B {y}
    Owned (F:=F) P Y y κ ((hitWidth P.p*v)*Real.exp (P.p.supportExponent+2)/κ)
      (fun U => (P.eval U:ℂ)* (if (flags P.p.threshold U ∩ Z).Nonempty then 1 else 0)) := by
  intro Z
  let T := fun _ : Unit => Z
  let f := fun _ : Unit => badge (G:=G) P.p.threshold Z
  let serial := WilsonCenteredLampCapture.docket (Unit × Finset ℕ)
  have anchor : y∈Z := halo_subset _ _ (mem_singleton_self _)
  have cover : coverNumber P.p.B Z ≤ 1 :=
    (Corona.list_cost _ (show covers P.p.B Z {y} from ⟨Subset.refl _,Corona.ship_halo _
      (by intro a ha b hb; rw [mem_singleton] at ha hb; subst a b; exact .refl)⟩)).trans_eq (card_singleton _)
  have cap : reservedMass P.p Z 1 ≤ Real.exp (P.p.supportExponent+2) := by
    rw [reservedMass,mul_one]
    apply Real.exp_monotone
    calc
      _ ≤ (P.p.supportExponent+2)*1 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast cover) (by linarith only [P.p.exponent_pos])
      _ = _ := mul_one _
  have income : SumBudget (fun i : Unit => reservedMass P.p (T i) 1) (Real.exp (P.p.supportExponent+2)) := by
    refine ⟨fun _ => by unfold reservedMass; positivity,summable_of_hasFiniteSupport (Set.toFinite _),?_⟩
    simpa [T,tsum_fintype] using cap
  have read (i : Unit) : Attaches P.p.threshold (T i) (f i) := attaches _ _
  have fee := WilsonCenteredFailedHalo.cost T K serial f (fun _=>1) quiet hv room (fun _=>zero_le_one)
    income (fun _ U=>by dsimp [f,badge]; split <;> simp)
  have fmt := WilsonCenteredCaptureSlots.formed P K T Quiet serial f y law (fun _ => anchor) read
  obtain ⟨h,form,rem,field⟩ := WilsonReceivedQuietCrownOwner.mounted (F:=F) Y y div _ fmt fee
  refine ⟨h,form,rem,fun U => ?_⟩
  rw [field]
  change (Real.exp (P.exponent U):ℂ)*(∑'Q,gasMark P.p P.activities U Q (entered P K T Quiet serial f))=_
  rw [WilsonCenteredFailedHalo.actual T K serial f read fee quiet U]
  simp only [tsum_fintype,Finset.univ_unique,Finset.sum_singleton,f,value,Rep.eval,Complex.ofReal_mul]
  ring

end YM.Integration.WilsonAddressedFlagIndicator
