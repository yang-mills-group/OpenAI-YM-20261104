import YM.Comparison.RG02.Valence.Amplify
import YM.Comparison.RG02.Bulk.Fk
/-!
# Sharp degree/rank grading on connected Fk

 `W` powers determine incoming mark ceilings. Price `σ` may be negative; may vary output index
 by index. Unmarked any order; permits singleton without any assumption on other costs.
 Includes field-independent constants. Fields are original *unconstrained* coarse log directions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Analysis YM.Marker YM.Multi Cumulants Cumulants.Wick Order Join Bulk
open YM.Extra.Trajectories (connected)
open YM.Next.Rank
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}
local notation "B"=> Board R r
variable (l : Hot R→ℕ) (t : R.Mode) (i : Index r)
def Toile (σ : V→ℤ) : Prop := ∀ p:Hot R,p.sites⊆t.val → l p ≤ 2+∑ v∈p.sites,σ v
private def duty (σ : V→ℤ) : V ⊕ Fin r →ℤ:= Sum.elim σ (fun _=>1)
private lemma whole (σ : V→ℤ) : ∑ v ∈ (pair t i).val, duty σ v=(∑ v∈t.val,σ v)+i.val.card := by
   simp [pair,duty,Finset.sum_disjSum]
private lemma collect_all (s : (parts (Board R r)).Mode) (σ : V→ℤ) : ∑ v∈(unionOf s).val,duty σ v=∑ a∈s.val,∑ v∈a.sites, duty σ v := sum_biUnion (parts_wise _)
lemma present (σ : V→ℤ) (h : Toile l t σ) (s : (parts (Board R r)).Mode) (hp : s∈shards (Board R r) (pair t i)) : (∑ a∈s.val,(zephyr l a : ℤ))+2-2*s.val.card ≤ i.val.card+2+∑ v∈t.val,σ v := by
   have hc := (mem_filter.mp hp).2
   change unionOf s=pair t i at hc
   have ht (a:Hot B) (ha:a∈s.val) : (zephyr l a:ℤ) ≤ 2+ ∑ v∈a.sites,duty σ v := by
      let w:= Join.left a.val
      have hv : a.val.val ⊆ (pair t i).val:= by rw [← hc]; intro z hz; exact mem_biUnion.mpr ⟨a,ha,hz⟩
      have hy : w.val ⊆ t.val:= left_pair t i ▸ (toLeft_subset_toLeft hv : w.val ⊆ (left (pair t i)).val)
      have hh : (∑ v∈a.sites,duty σ v)=(∑ v∈w.val,σ v)+(Join.right a.val).val.card := by
         exact (show _ from Eq.trans (congrArg (fun p:(Board R r).Mode=> ∑ v∈p.val,duty σ v) (pair_reunite a.val).symm) (whole w (Join.right a.val) σ))
      rw [hh,zephyr,Nat.cast_add,← add_assoc]; apply add_le_add_left
      unfold hairs; change ( (↑(if H : w.val.Nonempty then l ⟨w,H⟩ else 2)) : ℤ)≤ _
      split
      next H=> exact h ⟨w,H⟩ hy
      next H => rw [show w.val=∅ from not_nonempty_iff_eq_empty.mp H,sum_empty]; norm_num
   have he:= sum_le_sum ht; rw [sum_add_distrib, ← collect_all s σ,hc, whole t i σ] at he; simp only [sum_const,nsmul_eq_mul] at he
   omega

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Tree.Forest S.ratio) (w : S.Choices) (W : Bulk.Colors R G f)

local notation "X" => fieldDir G c 1
local notation "x₀" => ((1:ℝ),(0:Bulk.SliceDir S F G))
local notation "a" x => Fk K F w W x r
private lemma wearing (t' : (B).Mode) (n : ℤ) (h : ∀ s∈shards B t', (∑ i∈s.val,(zephyr W.power i:ℤ))+2-2*s.val.card≤n): Level n (fun x : X=> (connected (a x)).part t'):= by
   let L:X→L[ℝ] (Bulk.SliceDir S F G):= (ContinuousLinearMap.id ℝ _).prod (fderiv ℝ (K.b F) 0)
   let L':= ContinuousLinearMap.inr ℝ ℝ (Bulk.SliceDir S F G) ∘L L
   have he (x:X): Bulk.stage K F x=x₀+ L' x:=Prod.ext (add_zero _).symm (show classical (G:=G) S F (K.b F) x= 0+L x from (zero_add (L x)).symm)
   unfold Bulk.Fk; simp_rw [he]; exact weather _ _ _ _ _ _ _ _ L' n h

lemma read (σ : V→ℤ) (k:ℕ) (h : Toile W.power t σ) : Level (k+2+(∑ v∈t.val,σ v)) (fun x => (observe R r (connected (a x)) k).part t):= by
   unfold observe; split
   next hk => simp_rw [Poly.part_smul]; apply Level.factor; apply wearing (R:=R); intro q hh; simpa only [picked r hk] using present W.power t (pick r k) σ h q hh
   next hk=> exact Level.zero _

lemma log_v_part (s:(B).Mode) {x : Grade R r} (hx : UnitLeading x) : (logVac x).part s= if Join.left s=R.quiet then (connected x).part s else 0 := by
   suffices he : logVac x=bottom R r (connected x) by
      rw [he]; nth_rw 1 [← pair_reunite s]; rw [bottom_value]; split_ifs with h
      · rw [← h,pair_reunite]
      rfl
   exact (log_map (bottom R r) bottom_quiet hx).symm
lemma log_m_part (s:(B).Mode) {x : Grade R r} (hx : UnitLeading x) : (logMarked x).part s= if Join.left s=R.quiet then 0 else (connected x).part s := by
   have he:= log_full hx; rw [show logMarked x= connected x-logVac x by rw [he]; abel, Extra.Trajectories.part_sub, log_v_part _ hx]; split <;> simp
lemma vacuum_read (r k:ℕ): Level ((k+2 : ℕ):ℤ) (fun x => (observe R r (logVac (Fk K F w W x r)) k).part R.quiet):= by
   let σ:V→ℤ:=0; have hz : Toile W.power R.quiet σ:= by intro s hs; exact False.elim ( not_nonempty_empty (s.property.mono (α:=V) hs))
   have he (x:X): (observe R r (logVac (Fk K F w W x r)) k).part R.quiet=(observe R r (connected (Fk K F w W x r)) k).part R.quiet:= by
      unfold observe; split
      next H=> exact congrArg ((k.factorial:ℂ)⁻¹*·) ((log_v_part (pair R.quiet (pick r k)) (fk_unit K F w W x r)).trans (if_pos (left_pair ..)))
      next H=>rfl
   simp_rw [he]; simpa only [Census.quiet,sum_empty,add_zero,Nat.cast_add, Nat.cast_ofNat] using read (R:=R) R.quiet K F w W (r:=r) σ k hz
lemma mark_read (σ : V→ℤ) (t:R.Mode) (k:ℕ) (h : Toile W.power t σ) : Level (k+2+(∑ v∈t.val,σ v)) (fun x => (observe R r (logMarked (a x)) k).part t):= by
   by_cases hx:t=R.quiet
   · subst t
     have H (x:X) : (observe R r (logMarked (a x)) k).part R.quiet=0:= by
         unfold observe; split
         next H=>
           change _*(logMarked (Fk K F w W x r)).part _=0
           rw [log_m_part _ (fk_unit K F w W x r),left_pair,if_pos rfl,mul_zero]
         next=>rfl
     simp_rw [H]; exact Level.zero _
   have he (x:X): (observe R r (logMarked (a x)) k).part t=(observe R r (connected (a x)) k).part t:= by
      unfold observe; split
      next H=> exact congrArg ((k.factorial:ℂ)⁻¹*·) ((log_m_part (pair t (pick r k)) (fk_unit K F w W x r)).trans (if_neg (by rwa [left_pair])))
      next=> rfl
   simp_rw [he]; exact read t K F w W σ k h

local notation "fired" v => R.fire v
abbrev ribbon (j:V) : Hot R := ⟨R.fire j,singleton_nonempty j⟩
lemma solo (j:V) (k:ℕ) : Level ((k+ W.power (ribbon j):ℕ):ℤ) (fun x=> (observe R r (logMarked (a x)) k).part (R.fire j)):= by
   let q:=W.power (ribbon j)
   let σ(v:V):ℤ:=q-2
   have h : Toile W.power (fired j) σ:= by
      intro a' h
      obtain he|he := Finset.subset_singleton_iff.mp (show a'.sites⊆ {j} from h) -- order
      · exact False.elim (not_nonempty_empty (he ▸ (show a'.sites.Nonempty from a'.property)))
      rw [show a'=ribbon j from Subtype.ext (Subtype.ext he), show (ribbon j : Hot R).sites={j} from rfl,sum_singleton]; dsimp only [σ,q]; omega
   convert mark_read K F w W σ (R.fire j) k h using 1; simp only [Census.fire,sum_singleton,Nat.cast_add,σ,q]; omega
end YM.Comparison.RG02.Valence
