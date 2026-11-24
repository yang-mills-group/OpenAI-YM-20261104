import YM.Integration.WilsonCenteredHardWallet
import YM.Integration.WilsonCenteredOccupiedHardRead

/-! Put the complete hard mode and its two distinct proper-face owners in
original free hard slots. All prices are at the incoming hard exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredHardMount
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots WilsonCenteredHardWallet
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (H : Hard X P.p P.activities.forced P.activities.K o R)
    (w : V→ℝ) (hw : ∀ i,0<w i)
    {κ v : ℝ} (wallet : H.Paid w P.p.B P.p.supportExponent κ)
    (quiet : P.activities.KBound P.p v) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (K : Guard.Keeper P.p P.activities) (law : P.activities.ForcedFamily P.p)
    (Z : Support n) (y : Site n) (center : y∈Z)

def bill (p : BudgetPoint) (Z : Support n) (v m : ℝ) :=
  let b:=Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*m
  b+(hitWidth p*v)*b

theorem reaches (C : Finset ℕ) (j : ℕ) (live : j∈C) :
    Push.Local.patch P.activities j⊆ground P Z C := fun _ hx=>
  mem_union_right _ (mem_biUnion.mpr ⟨j,live,hx⟩)

def leg (s : R.Mode) (x : X) (i : ℕ) (U : Config G n) :=
  (H.hard x i U).part s

def mate (a b : V) (x : X) (z : ℕ×ℕ) (U : Config G n) :=
  if z.1=z.2 then 0 else leg H (R.fire a) x z.1 U*leg H (R.fire b) x z.2 U

def first (s : R.Mode) (x : X) (serial : ℕ×Finset ℕ ↪ ℕ) :=
  entered P K (fun _=>Z) unit serial (leg H s x)

def second (a b : V) (x : X) (serial : (ℕ×ℕ)×Finset ℕ ↪ ℕ) :=
  entered P K (fun _=>Z) pair serial (mate H a b x)

include hw wallet quiet hv room law center
theorem single (s : R.Mode) (u : V) (member : u∈s.val) (home : o u∈Z)
    (x : X) (serial : ℕ×Finset ℕ ↪ ℕ) :
    ForceFormat P.p P.activities y (first H K Z s x serial) ∧
    ForceCost P.p P.activities (first H K Z s x serial) (bill P.p Z v ((Poly.toll w s)⁻¹*κ)) := by
  obtain ⟨e,pos,touch,cap,paid⟩:=WilsonCenteredHardWallet.single H w hw s u member wallet Z home
  constructor
  · apply WilsonCenteredOwnerIntake.formed P (fun _=>Z) unit K serial (leg H s x) y law (fun _=>center)
    · intro i g U
      exact congrArg (fun k : Poly R=>k.part s) ((H.locality x i).gauge g U)
    · intro i;exact (Poly.part_cont _).measurable.comp (H.locality x i).borel
    intro i U V hg hf
    have model:=(H.locality x i).widen (reaches (P:=P) Z (unit i) i (mem_singleton_self _))
    exact congrArg (fun k : Poly R=>k.part s) (model.reads U V hg hf)
  unfold first
  exact WilsonCenteredOwnerIntake.cost P (fun _=>Z) unit K serial (leg H s x) e quiet hv room pos paid touch
    (fun i U=>cap i x U)

theorem twice (a b : V) (ha : o a∈Z) (hb : o b∈Z) (x : X) (serial : (ℕ×ℕ)×Finset ℕ ↪ ℕ) :
    ForceFormat P.p P.activities y (second H K Z a b x serial) ∧
    ForceCost P.p P.activities (second H K Z a b x serial) (bill P.p Z v (((w a)⁻¹*κ)*((w b)⁻¹*κ))) := by
  obtain ⟨e,k,pe,pk,touch,capA,capB,paid⟩:=WilsonCenteredHardWallet.couple H w hw a b wallet Z ha hb
  constructor
  · apply WilsonCenteredOwnerIntake.formed P (fun _=>Z) pair K serial (mate H a b x) y law (fun _=>center)
    · intro z g U
      simp only [mate,leg,(H.locality x z.1).gauge g U,(H.locality x z.2).gauge g U]
    · intro z
      change Measurable (fun U=>if z.1=z.2 then (0:ℂ) else (H.hard x z.1 U).part (R.fire a)*(H.hard x z.2 U).part (R.fire b))
      by_cases same : z.1=z.2
      · simpa only [mate,if_pos same] using (measurable_const : Measurable (fun _ : Config G n=>(0:ℂ)))
      simp only [if_neg same]
      have fa : Measurable (fun U=>(H.hard x z.1 U).part (R.fire a)) :=
        (Poly.part_cont _).measurable.comp (H.locality x z.1).borel
      have fb : Measurable (fun U=>(H.hard x z.2 U).part (R.fire b)) :=
        (Poly.part_cont _).measurable.comp (H.locality x z.2).borel
      exact fa.mul fb
    intro z U V hg hf
    have firstR:=(H.locality x z.1).widen (reaches (P:=P) Z (pair z) z.1 (mem_insert_self ..))
    have lastR:=(H.locality x z.2).widen (reaches (P:=P) Z (pair z) z.2 (mem_insert_of_mem (mem_singleton_self _)))
    simp only [mate,leg,firstR.reads U V hg hf,lastR.reads U V hg hf]
  unfold second
  have pos z : 0≤joined e k z := by
    by_cases same : z.1=z.2
    · simp [joined,same]
    simpa [joined,same] using mul_nonneg (pe z.1) (pk z.2)
  apply WilsonCenteredOwnerIntake.cost P (fun _=>Z) pair K serial (mate H a b x) (joined e k) quiet hv room pos paid touch
  intro z U
  by_cases same : z.1=z.2
  · simp [mate,joined,same]
  simpa only [mate,leg,joined,if_neg same,norm_mul] using mul_le_mul (capA z.1 x U) (capB z.2 x U) (norm_nonneg _) (pe _)

end YM.Integration.WilsonCenteredHardMount
