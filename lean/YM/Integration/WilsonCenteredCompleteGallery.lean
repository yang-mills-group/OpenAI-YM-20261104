import YM.Integration.WilsonCenteredMixedSetRead
import YM.Integration.WilsonCenteredMaskPieces

/-! Capture the complete marked density on its original receiving Wilson
gallery. The regular-only source and signed regular packets use their genuine
rooted funding. Every mixed or all-hard face is built here on the same Keeper. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCompleteGallery
open Finset RG Wilson Lattice Marker QuadraticLocal Source Labels Extra.Histories Push.Local Planned.GuardedAtom
open WilsonCenteredFiledAtoms WilsonCenteredMaskPieces WilsonCenteredSoftInventory
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}
    (A : Gallery X ι o P R) (x : X) (S : SectionData F) (Y : Hol G) (Z : Support n) (y : Site n)

def soft (t : R.Mode) (U : Config G n) := (Poly.pass (A.E.log x U)).part t

def share (z : R.Mode×R.Mode) (U : Config G n) :=
  (Real.exp (P.exponent U):ℂ)*(soft A x z.1 U*(A.gas x U).part z.2)

def invoice (p : BudgetPoint) (s : R.Mode) (w : V→ℝ) (v κ bare : ℝ) (rows : R.Mode→ℝ) :=
  ∑z∈splits s,if z.2=R.quiet then bare else
    (WilsonCenteredMixedSetFiling.price (rows z.1) w z.2 κ +
      (hitWidth p*v)*WilsonCenteredMixedSetFiling.price (rows z.1) w z.2 κ)/κ

theorem original (s : R.Mode) (resident : ∀v∈s.val,o v∈Z) (center : y∈Z)
    (K : Guard.Keeper P.p P.activities) (w : V→ℝ) (hw : ∀v,0<w v) {σ C Λ δ v κ : ℝ}
    (law : P.Lawful σ C Λ δ v) (hv : 0≤v) (room : hitWidth P.p*v≤1) (div : 0<κ)
    (paid : A.K.Paid w P.p.B P.p.supportExponent κ)
    (old : ∀ U,Summable (Fusion.Attached.packet P.activities P.p (A.K.hard x) U))
    (rows : R.Mode→ℝ) (publish : ∀t,t.val⊆s.val→Receipt P Z (soft A x t) (rows t))
    (bare : ℝ) (regular : Store P S Y y κ bare (fun U=>(P.eval U:ℂ)*soft A x s U)) :
    Store P S Y y κ (invoice P.p s w v κ bare rows) (fun U=>(A.density x U).part s) :=by
  let fee (z : R.Mode×R.Mode) :=if z.2=R.quiet then bare else
    (WilsonCenteredMixedSetFiling.price (rows z.1) w z.2 κ+(hitWidth P.p*v)*WilsonCenteredMixedSetFiling.price (rows z.1) w z.2 κ)/κ
  have face (z) (present : z∈splits s) : Store P S Y y κ (fee z) (share A x z) :=by
    have census:=valid present
    by_cases vacant : z.2=R.quiet
    · have left : z.1=s :=Subtype.ext (by simpa [vacant,Census.quiet] using census.2)
      obtain ⟨q,fit,cap,ok⟩:=regular
      refine ⟨q,fit,by simpa only [fee,if_pos vacant] using cap,fun U=>?_⟩
      have noMark := Hard.packet_of_quiet A.K x U (old U)
      change (A.gas x U).part R.quiet=(P.activities.gas P.p U:ℂ) at noMark
      rw [ok,share,left,vacant,noMark]
      simp only [Rep.eval,Complex.ofReal_mul]
      ring
    have hleft : z.1.val⊆s.val :=census.2 ▸ subset_union_left
    have hright : z.2.val⊆s.val :=census.2 ▸ subset_union_right
    have receipt:=WilsonCenteredMixedSetRead.original (publish z.1 hleft) A.K K S Y z.2 vacant x y center
      (fun a ha=>resident a (hright ha)) law.labels.forced w hw div paid law.labels.boundK hv room old
    obtain ⟨q,fit,cap,oath⟩:=receipt
    exact ⟨q,fit,by simpa only [fee,if_neg vacant] using cap,fun U=>oath U⟩
  have sumAll (f : Finset (R.Mode×R.Mode)) (inside : f⊆splits s) :
      Store P S Y y κ (∑z∈f,fee z) (fun U=>∑z∈f,share A x z U) :=by
    induction f using Finset.induction_on with
    | empty =>
      obtain ⟨q,h,r,oath⟩:=WilsonCenteredFiledAtoms.empty (P:=P) S Y y div
      exact ⟨q,h,by simpa using r,fun U=>by simpa using oath U⟩
    | insert z f hz ih =>
      obtain ⟨zfit,tail⟩:=insert_subset_iff.mp inside
      obtain ⟨q,h,r,oath⟩:=add law div (face z zfit) (ih tail)
      exact ⟨q,h,by simpa only [sum_insert hz] using r,
        fun U=>by simpa only [sum_insert hz,Pi.add_apply] using oath U⟩
  obtain ⟨q,fit,cap,oath⟩:=sumAll (splits s) Subset.rfl
  exact ⟨q,fit,cap,fun U=>(oath U).trans (WilsonCenteredMaskPieces.density A x U s).symm⟩

end YM.Integration.WilsonCenteredCompleteGallery
