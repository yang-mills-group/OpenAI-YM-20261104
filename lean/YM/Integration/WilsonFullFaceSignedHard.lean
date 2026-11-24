import YM.Integration.WilsonCenteredCompleteGallery
import YM.Integration.WilsonCapturedPrimarySoftInventory

/-! The complete occupied hard part of an ordinary Wilson face on its own
representation. Each nonempty hard split spends its actual marked hit before
one division by the physical allowance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFullFaceSignedHard
open Finset RG Wilson Lattice Marker QuadraticLocal Source Labels Extra.Histories Push.Local Planned.GuardedAtom
open WilsonCenteredFiledAtoms WilsonCenteredMaskPieces WilsonCenteredSoftInventory
open WilsonCenteredOccupiedHardSets WilsonCenteredMixedSetFiling WilsonCenteredCompleteGallery
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}

theorem collect {I : Type} (s : Finset I) (S : SectionData F) (Y : Hol G) (y : Site n)
    {κ σ C Λ δ v : ℝ} (div : 0<κ) (law : P.Lawful σ C Λ δ v)
    (fees : I→ℝ) (faces : I → Config G n→ℂ)
    (paid : ∀a∈s,Store P S Y y κ (fees a) (faces a)) :
    Store P S Y y κ (∑a∈s,fees a) (fun U=>∑a∈s,faces a U) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨q,fit,bill,field⟩ := WilsonCenteredFiledAtoms.empty (P:=P) S Y y div
    exact ⟨q,fit,by simpa only [sum_empty] using bill,fun U=>by simpa only [sum_empty,Pi.zero_apply] using field U⟩
  | insert a s h ih =>
    obtain ⟨q,fit,cap,field⟩ := WilsonCenteredFiledAtoms.add law div
      (paid a (mem_insert_self ..)) (ih (fun j hj=>paid j (mem_insert_of_mem hj)))
    exact ⟨q,fit,by simpa only [sum_insert h] using cap,
      fun U=>by simpa only [sum_insert h,Pi.add_apply] using field U⟩

def occupied {R : Census V} (s : R.Mode) := (splits s).filter (fun z=>z.2≠R.quiet)

def fee {R : Census V} (p : BudgetPoint) (Z : Support n) (w : V→ℝ)
    (s : R.Mode) (C ε v κ : ℝ) :=
  ∑z∈occupied s, (1+hitWidth p*v)*price (WilsonCapturedPrimarySoftInventory.fare p Z w C z.1) w z.2 ε / κ

theorem original [Countable ι] (A : Gallery X ι o P R) (x : X) (s : R.Mode)
    (S : SectionData F) (Y : Hol G) (Z : Support n) (y : Site n)
    (center : y∈Z) (resident : ∀j∈s.val,o j∈Z)
    (K : Guard.Keeper P.p P.activities) (w : V→ℝ) (hw : ∀v,0<w v) {σ C Λ δ v κ ε E : ℝ}
    (law : P.Lawful σ C Λ δ v) (hv : 0≤v) (room : hitWidth P.p*v≤1) (div : 0<κ)
    (regular : A.E.Paid w P.p.B (P.p.supportExponent+2) E)
    (paid : A.K.Paid w P.p.B P.p.supportExponent ε) :
    Store P S Y y κ (fee P.p Z w s E ε v κ)
      (fun U=>(A.density x U).part s-(P.eval U:ℂ)*soft A x s U) :=by
  have old := Hard.packet_summing A.K paid P.p.exponent_pos.le hw x
  let rows (t:R.Mode) := WilsonCapturedPrimarySoftInventory.fare P.p Z w E t
  let cost (z:R.Mode×R.Mode) := (1+hitWidth P.p*v)*price (rows z.1) w z.2 ε / κ
  have face (z : R.Mode×R.Mode) (relevant : z∈occupied s) : Store P S Y y κ (cost z) (share A x z) :=by
    obtain ⟨present,live⟩:=mem_filter.mp relevant
    have census:=valid present
    have left : z.1.val⊆s.val:=census.2 ▸ subset_union_left
    have right : z.2.val⊆s.val:=census.2 ▸ subset_union_right
    let e := (WilsonCapturedPrimarySoftInventory.original A.E x z.1 Z
      (fun j hj=>resident j (left hj)) w hw regular).some
    letI : Countable e.Row := e.counted
    letI := Encodable.ofCountable ((e.Row×Chosen)×Finset ℕ)
    let serial : (e.Row×Chosen)×Finset ℕ ↪ ℕ := ⟨Encodable.encode,Encodable.encode_injective⟩
    obtain ⟨format,charge⟩:=WilsonCenteredMixedSetFiling.original e A.K K z.2 x y center
      (fun j hj=>resident j (right hj)) serial law.labels.forced w hw paid law.labels.boundK hv room
    obtain ⟨q,fit,bill,field⟩:=WilsonCenteredHardFiled.source S Y y div _ format charge
    exact ⟨q,fit,by simpa only [cost,rows,add_mul,one_mul] using bill,fun U=>
      (field U).trans (congrArg (fun t=>(Real.exp (P.exponent U):ℂ)*t)
        (WilsonCenteredMixedSetRead.grouped e A.K K z.2 live x U serial charge law.labels.boundK (old U)))⟩
  obtain ⟨q,fit,bill,field⟩:=collect (occupied s) S Y y div law cost (share A x) face
  refine ⟨q,fit,bill,fun U=>?_⟩
  have blank : (s,R.quiet)∈splits s:=by
    apply mem_filter.mpr
    exact ⟨mem_univ _,by simp [Poly.merges,Census.quiet]⟩
  have comp (z : R.Mode×R.Mode) (hz : z∈splits s) : z.2=R.quiet ↔ z=(s,R.quiet) :=by
    constructor
    · intro empty
      exact Prod.ext (Subtype.ext (by simpa [empty,Census.quiet] using (valid hz).2)) empty
    · rintro rfl; rfl
  have erase : occupied s=(splits s).erase (s,R.quiet):=by
    ext z; simp only [occupied,mem_filter,mem_erase]
    exact ⟨fun h=>⟨fun e=>h.2 ((comp z h.1).2 e),h.1⟩,
      fun h=>⟨h.2,fun eq=>h.1 ((comp z h.2).1 eq)⟩⟩
  have quiet:=Hard.packet_of_quiet A.K x U (old U)
  change (A.gas x U).part R.quiet=(P.activities.gas P.p U:ℂ) at quiet
  have one : share A x (s,R.quiet) U=(P.eval U:ℂ)*soft A x s U :=by
    rw [share,quiet]; simp only [Rep.eval,Complex.ofReal_mul];ring
  rw [field,erase]
  change (∑ z∈(splits s).erase (s,R.quiet),share A x z U)=(A.density x U).part s-(P.eval U:ℂ)*soft A x s U
  rw [WilsonCenteredMaskPieces.density,←one]
  exact (eq_sub_iff_add_eq).2 (sum_erase_add (splits s) (fun z=>share A x z U) blank)

end YM.Integration.WilsonFullFaceSignedHard
