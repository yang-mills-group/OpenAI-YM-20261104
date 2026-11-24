import YM.MSbar.Fiber.Erode
import YM.Push.BETA_TRANSPORT.Activity

/-! # Reposition a window. Used for real finite-difference SD. 
Leaf scoping READ enlarged exactly for shifted masks including external legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bulk
open Lattice Wilson RG Filter Function MeasureTheory PhysicalNext.Repeat.Lotus
open Push Finset Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{R:Rep G f}
def need (R:Rep G f) (i:ℕ):=(R.activities.forced i).support
def seen (R:Rep G f) (i:ℕ):=(R.activities.forced i).inventory
variable {U:Type*}{a σ C δ Λ w:ℝ}
variable (R) (X:Support f) (κ: Config G f→ Config G f) (g:Config G f→ℝ)
structure Tracks (S:StepData c f)(a:ℝ) : Prop where
  routes : S.Inner g
  sizes : UsesFinal R.p.threshold X g
  track : Measurable g
  blood U: |g U| ≤ a
  live : Measurable κ
  paid U : g U≠0 → flags R.p.threshold (κ U)=flags R.p.threshold U
  -- stamper must be able to work on EACH larger queried support (inspected extra known via mask test!)
  detects U V Y : g U≠0 → X ⊆ Y→ Agrees (Y:Set _) U V → Y∩ flags R.p.threshold U = Y ∩ flags R.p.threshold V → Agrees Y (κ U) (κ V)
  turns k U: (∀ i,k (S.ratio.embed i)=1) → g U≠0→ κ (gauge k U)= gauge k (κ U)
  localOp Y U: g U≠0→ Disjoint X Y → Agrees (Y:Set _) U (κ U)
-- localVariations : all forced partners whose support touches any link. Others have K unchanged.
variable {R X κ g}
variable (A:Support f)
lemma reads_small {X Y : Support f} (hx:X⊆Y) (v u:Support f) (hp:Y∩v=Y∩u):X∩v=X∩u:=by rw [show X=X∩Y from (inter_eq_left.mpr hx).symm, inter_assoc, hp, inter_assoc]

namespace Recenter
variable (X) (T:Tracks R X κ g S a)
def Kindle (R:Rep G f) (X : Support f) : Set (Finset ℕ):={p | p.Nonempty∧ (∀ i∈p,¬Disjoint X (need R i)) ∧ (p:Set ℕ).PairwiseDisjoint (need R)}
abbrev Chunk (R:Rep G f)(X:Support f):=Subtype (Kindle R X)
def extent (p:Chunk R X):= X∪p.val.biUnion (need R)
def lore (p:Chunk R X):=p.val.biUnion (seen R)
variable (h:R.Lawful σ C Λ δ w)(K:MergeProof.Menu.Arsenal R)
variable {X}
lemma sure (p:Chunk R X) : MergeProof.Accent.Sure (extent X p,lore X p):=by
    refine ⟨?_,fun v hv=>?_⟩
    · obtain ⟨i,hi⟩:=p.prop.1; exact ((R.activities.forced i).inventory_ne).mono (Finset.subset_biUnion_of_mem (seen R) hi)
    obtain ⟨j,hj,hk⟩:=mem_biUnion.mp hv; exact mem_union_right _ (mem_biUnion.mpr ⟨j,hj,(R.activities.forced j).inventory_sup hk⟩)
def tag (p:Chunk R X):=(K.wet _ (sure p)).choose
lemma chosen (p:Chunk R X) : need R (tag K p) = extent X p ∧ seen R (tag K p) = lore X p∧∀ U,extent X p∩ flags R.p.threshold U=lore X p → (R.activities.forced (tag K p)).eligible R.p.threshold U:=by
   obtain ⟨h,hf⟩:= (K.wet _ (sure p)).choose_spec; exact ⟨Prod.mk.inj h|>.1,Prod.mk.inj h|>.2,hf⟩
def fare (p:Chunk R X)(B:Finset ℕ):= (insert (tag K p) (B \ p.val))
def toll (κ:Config G f→ Config G f)(g:Config G f→ℝ)(p:Chunk R X)(U:Config G f):= if extent X p∩ flags R.p.threshold U=lore X p then g U*( (∏ i∈p.val, R.activities.K i (κ U))-(∏ i∈p.val,R.activities.K i U)) else 0
variable (b:ℕ→ℝ)(hg:∀ i,0 ≤ b i ∧ ∀ U,‖R.activities.K i U‖ ≤ b i)
local notation "c!" => R.activities
lemma tag_borel (p:Chunk R X) : MeasurableSet {U:Config G f | extent X p∩flags R.p.threshold U=lore X p}:=by
    rw [show {U:Config G f | _}= ⋃ s∈ Finset.univ.filter (fun s=> extent X p∩s=lore X p),{U:Config G f | flags R.p.threshold U=s} from by ext; simp]; refine MeasurableSet.iUnion fun i=>MeasurableSet.iUnion fun _=>RG.flags_measurable_eq ..
include T h
def pay (p:Chunk R X): Fibre S R where
   turn:= Wing.gasKey (tag K p)
   ingredient:= toll κ g p
   scopedR:= by
     change UsesFinal R.p.threshold (need _ _) _; rw [(chosen K p).1]
     intro U V hu hv; let Y:=extent X p
     have hX:X⊆Y:=Finset.subset_union_left
     have hy:g U=g V:= T.sizes U V (agrees_mono hu (coe_subset.mpr hX)) (reads_small hX _ _ hv)
     unfold toll; rw [hv]; split
     next hj=>
       by_cases hh:g U=0
       · rw [hh,← hy,hh,zero_mul,zero_mul]
       have hh' := T.detects _ _ Y hh hX hu hv; have hx:= T.paid _ hh; have hz:= T.paid V (by rwa [← hy]); have hh₀:Y∩ flags R.p.threshold (κ U)=Y∩flags R.p.threshold (κ V) :=by rw [hx,hz,hv]
       have hk(i : ℕ)(he:i∈p.val): need R i ⊆ Y:= (subset_biUnion_of_mem (need R) he).trans Finset.subset_union_right; have hK:=h.labels.forced.reads
       rw [hy]; apply congr_arg; exact congr_arg₂ (· - ·) (prod_congr rfl fun i hi=> hK i _ _ (agrees_mono hh' (coe_subset.mpr (hk i hi))) (reads_small (hk i hi) _ _ hh₀)) (prod_congr rfl fun i hi=> hK i _ _ (agrees_mono hu (coe_subset.mpr (hk i hi))) (reads_small (hk i hi) _ _ hv))
     rfl
   grant := fun U he=>(chosen K p).2.2 U (by unfold toll at he; split at he; assumption; exact (he rfl).elim)
   blank:= trivial
   weight:= (a*2)*∏ i∈p.val,b i
   earn := by
       intro U; have hh i (hi:i∈p.val):0≤ b i:=(hg i).1
       have hp := Finset.prod_nonneg hh; have ha:= T.blood U
       unfold toll; split
       next=>
          let t:= ∏ i∈p.val,b i
          have hH(U) : ‖∏ i∈p.val, R.activities.K i U‖ ≤ t:= by rw [norm_prod]; exact Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>(hg i).2 _)
          rw [norm_mul,mul_assoc,two_mul]; apply mul_le_mul ha; exact (norm_sub_le ..).trans (add_le_add (hH _) (hH _)); exact norm_nonneg _; exact (abs_nonneg _).trans ha
       rw [norm_zero]; exact mul_nonneg (mul_nonneg ((abs_nonneg _).trans ha) zero_le_two) hp
   borel:= by refine Measurable.ite (tag_borel p) (T.track.mul ((Finset.measurable_fun_prod _ fun i _=> (h.labels.forced.meas i).comp T.live).sub (Finset.measurable_fun_prod _ fun i _=> h.labels.forced.meas i))) measurable_const
   glows:=fun t ht U=>by
      unfold toll; rw [gauge_flags]; split_ifs
      next h₀=>
        rw [T.routes t ht]; by_cases hp:g U=0; rw [hp,zero_mul,zero_mul]
        rw [T.turns t U ht hp]; exact congr_arg _ (congr_arg₂ (·-·) (prod_congr rfl fun i _=> h.labels.forced.sym i t _) (prod_congr rfl fun i _=> h.labels.forced.sym i t _))
      next _ => rfl
end Recenter
end YM.MSbar.Bulk
