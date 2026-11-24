import YM.Integration.WilsonCenteredOccupiedHardSets
import YM.Integration.WilsonCenteredHardMount

/-! File arbitrary occupied hard subwords on the actual Keeper's original
addresses, absorbing all quiet owners meeting the complete ground. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredHardSetFiling
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local
open WilsonCenteredOccupiedFamilies WilsonCenteredOccupiedHardSets WilsonCenteredKeptOwners
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots WilsonCenteredHardMount
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (H : Hard X P.p P.activities.forced P.activities.K o R)
    (K : Guard.Keeper P.p P.activities) (Z : Support n)

theorem dye_continuous (s : R.Mode) : Continuous (dye s : Poly R→Poly R) := by
  apply Continuous.sub
  · apply continuous_pi
    intro t
    change Continuous (fun A : Poly R=>(WilsonCenteredSubmask.cut s A).part t)
    simp only [WilsonCenteredSubmask.tested]
    split <;> first | exact Poly.part_cont _ | exact continuous_const
  exact (Poly.part_cont R.quiet).smul continuous_const

def reading (s : R.Mode) (x : X) (I : Chosen) (U : Config G n) := (word H s I x U).part s

def host (s : R.Mode) (x : X) (serial : Chosen×Finset ℕ ↪ ℕ) :=
  entered P K (fun _=>Z) Subtype.val serial (reading H s x)

/-- Fortified original hard term with its once-divided invoice. -/
theorem original (s : R.Mode) (x : X) (y : Site n) (center : y∈Z) (home : ∀v∈s.val,o v∈Z)
    (serial : Chosen×Finset ℕ ↪ ℕ) (law : P.activities.ForcedFamily P.p)
    (w : V→ℝ) (hw : ∀v,0<w v) {κ v : ℝ} (paid : H.Paid w P.p.B P.p.supportExponent κ)
    (quiet : P.activities.KBound P.p v) (hv : 0≤v) (room : hitWidth P.p*v≤1) :
    ForceFormat P.p P.activities y (host H K Z s x serial) ∧
    ForceCost P.p P.activities (host H K Z s x serial)
      (bill P.p Z v ((Poly.toll w s)⁻¹*(Real.exp (s.val.card*κ)-1))) :=by
  obtain ⟨k,pos,touches,cap,price⟩:=WilsonCenteredOccupiedHardSets.original H w hw s Z home paid
  have ticket := inv_pos.mpr (Poly.worth hw s)
  constructor
  · apply WilsonCenteredOwnerIntake.formed P (fun _=>Z) Subtype.val K serial (reading H s x) y law (fun _=>center)
    · intro I g U
      unfold reading word
      apply congrArg (fun A : Poly R=>A.part s)
      exact Finset.prod_congr rfl (fun j _=>congrArg (dye s) ((H.locality x j).gauge g U))
    · intro I
      apply (Poly.part_cont s).measurable.comp
      exact Finset.measurable_fun_prod _ (fun j _=>(dye_continuous s).measurable.comp (H.locality x j).borel)
    intro I U U' hg hf
    unfold reading word
    apply congrArg (fun A : Poly R=>A.part s)
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (dye s) (((H.locality x j).widen (reaches (P:=P) Z I.val j hj)).reads U U' hg hf)
  apply WilsonCenteredOwnerIntake.cost P (fun _=>Z) Subtype.val K serial (reading H s x) (fun I=>(Poly.toll w s)⁻¹*k I)
    quiet hv room (fun I=>mul_nonneg ticket.le (pos I))
  · have sw:=sumBudget_mul_left price ticket.le
    have h:=sumBudget_mul_left sw (Real.exp_pos ((P.p.supportExponent+2)*coverNumber P.p.B Z)).le
    convert h using 1
    ext I
    simp only [reservedMass,salary]
    ring
  · intro I used
    exact touches I ((mul_ne_zero_iff.mp used).2)
  intro I U
  have h:=Poly.member hw s (word H s I x U)
  apply (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left (h.trans (cap I x U)) ticket.le)
  unfold reading
  field_simp [ne_of_gt (Poly.worth hw s)]

end YM.Integration.WilsonCenteredHardSetFiling
