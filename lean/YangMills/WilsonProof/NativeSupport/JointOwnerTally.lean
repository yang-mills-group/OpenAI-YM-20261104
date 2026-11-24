import YangMills.WilsonProof.NativeSupport.JointOwnerHeap

/-! The one-owner price survives the actual tally of native regular
fragrances and forced barcodes. Each fiber is summed before taking its
coordinate, using the same summability receipt as the unmarked tally. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.NativeSwitch
open Function Finset Lattice RG Wilson Marker Merge.Switch Extra.Trajectories
open MergeProof MergeProof.Menu MergeProof.Accent
open scoped BigOperators Classical
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V] {B : Census V}
variable {G : Gauge} {n : Side} {R : Rep G n}
variable (q : I → Hat B R) (w : V→ℝ) (active : Finset V)
variable (origin : ∀ i,∃ v∈(q i).s.val,v∈active)
variable (p : B.Mode) (y : V) (only : p.val∩active={y})
variable {J K X : Type} (key : J→K) (f : J→X→Ways (Mound q)) (j : K) (U : X)
local notation "phase" => (Stock.census Unit).fire ()
local notation "plant" => (fun i=>sing (heap q i) w)
local notation "probe" i => singleProbe (Sum.inl i : Mound q)
include origin only in
theorem tally_one_owner
    (whole : Summable fun a=>sound plant (f a U))
    (one : ∀ i:I,Summable fun a=>sound (probe i) (f a U)) :
    (tally key (fun a Z=>sound plant (f a Z)) j U).part p =
      ∑ i:I,(tally key (fun a Z=>sound (probe i) (f a Z)) j U).part phase *
        (sing (q i) w).part p := by
  let T := {a : J // key a=j}
  have full : Summable (fun a:T=>sound plant (f a.val U)) :=
    whole.comp_injective (i:=Subtype.val (p:=fun a=>key a=j)) Subtype.val_injective
  have small (i:I) : Summable (fun a:T=>sound (probe i) (f a.val U)) :=
    (one i).comp_injective (i:=Subtype.val (p:=fun a=>key a=j)) Subtype.val_injective
  have hs (i:I) : Summable (fun a:T=>(sound (probe i) (f a.val U)).part phase) :=
    ((small i).hasSum.map
      (Poly.get phase).toAddMonoidHom (Poly.get phase).continuous).summable
  rw [tally,Poly.share full]
  simp_rw [mounted_one_owner q w active origin p y only]
  rw [Summable.tsum_finsetSum]
  · apply sum_congr rfl
    intro i _
    rw [tsum_mul_right,tally,Poly.share (small i)]
  · intro i _
    exact (hs i).mul_right _

omit [DecidableEq I] in
include origin in
theorem tally_without_owner (away : Disjoint p.val active) (hot : p≠B.quiet)
    (whole : Summable fun a=>sound plant (f a U)) :
    (tally key (fun a Z=>sound plant (f a Z)) j U).part p=0 := by
  let T := {a : J // key a=j}
  have full : Summable (fun a:T=>sound plant (f a.val U)) :=
    whole.comp_injective (i:=Subtype.val (p:=fun a=>key a=j)) Subtype.val_injective
  rw [tally,Poly.share full]
  refine (tsum_congr (g:=fun (_:T)=>0) ?_).trans tsum_zero
  intro j₀
  let s (i:Mound q) := (heap q i).s
  let c (i:Mound q) := (heap q i).charge/(sumFee (heap q i) w : ℂ)
  have rooted (i : Mound q) : ∃ v∈(s i).val,v∈active := by
    cases i with
    | inl j => exact origin j
    | inr j =>
      obtain ⟨a,ha⟩ := j.2.val.property.1
      obtain ⟨v,hv,act⟩ := origin a
      exact ⟨v,mem_biUnion.mpr ⟨a,ha,hv⟩,act⟩
  change (sound (fun i=>Poly.send (s i) (c i)) _).part p=0
  rw [sound,mapScores_apply,Poly.part_sum]
  apply sum_eq_zero
  intro T _
  rw [Poly.part_smul]
  apply mul_eq_zero_of_right
  by_cases h : T.Nonempty
  · by_contra hz
    have h' : (∏ j∈T,Poly.send (s j) (c j))≠0 := fun eq=>hz (by rw [eq]; rfl)
    have fit := fits_of_tagged_prod s h'
    rw [tagged_prod s T fit,Poly.part_send] at hz
    have eq : p=unionTag s T fit := by_contra fun bad=>hz (if_neg bad)
    obtain ⟨a,ha⟩:=h
    obtain ⟨v,hv,act⟩:=rooted a
    exact disjoint_left.mp away (eq ▸ mem_biUnion.mpr ⟨a,ha,hv⟩) act
  · rw [Finset.not_nonempty_iff_eq_empty.mp h,prod_empty,Poly.one_part,if_neg hot]

end YM.Integration.InletSusceptibility.NativeSwitch
