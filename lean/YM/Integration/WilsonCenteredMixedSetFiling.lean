import YM.Integration.WilsonCenteredHardSetFiling
import YM.Integration.WilsonCenteredSoftInventory

/-! Mount a complete regular face times a nonempty hard face. Every original
quiet owner meeting the whole regular ground is absorbed before taking a read. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredMixedSetFiling
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local Push.AbsoluteSums
open WilsonCenteredOccupiedFamilies WilsonCenteredOccupiedHardSets WilsonCenteredKeptOwners
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots WilsonCenteredHardMount
open WilsonCenteredHardSetFiling WilsonCenteredSoftInventory
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} {Z : Support n} {Q : Config G n→ℂ} {b : ℝ} (E : Receipt P Z Q b)
    (H : Hard X P.p P.activities.forced P.activities.K o R)
    (K : Guard.Keeper P.p P.activities)

def sample (s : R.Mode) (x : X) (a : E.Row×Chosen) (U : Config G n) :=
  E.value a.1 U*reading H s x a.2 U

def placed (s : R.Mode) (x : X) (serial : (E.Row×Chosen)×Finset ℕ ↪ ℕ) :=
  entered P K (fun a : E.Row×Chosen=>E.ground a.1) (fun a=>a.2.val) serial (sample E H s x)

def price (b : ℝ) (w : V→ℝ) (s : R.Mode) (κ : ℝ) := b*((Poly.toll w s)⁻¹*(Real.exp (s.val.card*κ)-1))

theorem original (s : R.Mode) (x : X) (y : Site n) (center : y∈Z) (resident : ∀v∈s.val,o v∈Z)
    (serial : (E.Row×Chosen)×Finset ℕ ↪ ℕ) (law : P.activities.ForcedFamily P.p)
    (w : V→ℝ) (hw : ∀v,0<w v) {κ v : ℝ} (paid : H.Paid w P.p.B P.p.supportExponent κ)
    (vac : P.activities.KBound P.p v) (hv : 0≤v) (room : hitWidth P.p*v≤1) :
    ForceFormat P.p P.activities y (placed E H K s x serial) ∧
    ForceCost P.p P.activities (placed E H K s x serial)
      (price b w s κ+(hitWidth P.p*v)*price b w s κ) :=by
  obtain ⟨k,pos,touches,cap,hfare⟩:=WilsonCenteredOccupiedHardSets.original H w hw s Z resident paid
  have ticket := inv_pos.mpr (Poly.worth hw s)
  constructor
  · apply WilsonCenteredOwnerIntake.formed P (fun a : E.Row×Chosen=>E.ground a.1) (fun a=>a.2.val)
      K serial (sample E H s x) y law (fun a=>E.holds a.1 center)
    · intro a g U
      unfold sample reading word
      rw [E.gauge a.1 g U]
      apply congrArg (fun B : Poly R=>E.value a.1 U*B.part s)
      exact prod_congr rfl (fun j _=>congrArg (dye s) ((H.locality x j).gauge g U))
    · intro a
      apply (E.borel a.1).mul
      apply (Poly.part_cont s).measurable.comp
      exact Finset.measurable_fun_prod _ (fun j _=>(dye_continuous s).measurable.comp (H.locality x j).borel)
    intro a U U' hg hf
    have sub : E.ground a.1⊆ground P (E.ground a.1) a.2.val:=subset_union_left
    have flags' :=congrArg (fun z=>E.ground a.1∩z) hf
    have lo := E.uses a.1 U U' (agrees_mono hg sub)
      (by simpa only [←inter_assoc,inter_eq_left.mpr sub] using flags')
    unfold sample reading word
    rw [lo]
    apply congrArg (fun B : Poly R=>E.value a.1 U'*B.part s)
    apply prod_congr rfl
    intro j hj
    exact congrArg (dye s) (((H.locality x j).widen (reaches (P:=P) (E.ground a.1) a.2.val j hj)).reads U U' hg hf)
  let e (a : E.Row×Chosen) :=E.price a.1*((Poly.toll w s)⁻¹*k a.2)
  apply WilsonCenteredOwnerIntake.cost P (fun a : E.Row×Chosen=>E.ground a.1) (fun a=>a.2.val) K serial
    (sample E H s x) e vac hv room (fun a=>mul_nonneg (E.nonnegative _) (mul_nonneg ticket.le (pos _)))
  · unfold price
    have bill:=budget_prod E.cash (sumBudget_mul_left hfare ticket.le)
    convert bill using 1
    ext a
    simp only [e,reservedMass,salary]
    ring
  · intro a used j present
    have active : k a.2≠0 :=fun h=>used (by simp [e,h])
    obtain ⟨u,hit,on⟩:=touches a.2 active j present
    exact ⟨u,E.holds a.1 hit,on⟩
  intro a U
  have single : ‖reading H s x a.2 U‖≤(Poly.toll w s)⁻¹*k a.2 :=by
    apply (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left ((Poly.member hw s (word H s a.2 x U)).trans (cap a.2 x U)) ticket.le)
    unfold reading
    field_simp [ne_of_gt (Poly.worth hw s)]
  exact (norm_mul _ _).le.trans (mul_le_mul (E.cap a.1 U) single (norm_nonneg _) (E.nonnegative _))

end YM.Integration.WilsonCenteredMixedSetFiling
