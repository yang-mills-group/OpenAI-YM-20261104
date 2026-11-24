import YM.FormalBulk08.Dawn.Tau

/-! Billed Taylor subtraction in canon coordinates. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dawn
open Filter Function Set Tensor Lattice Chapel Maxwell
open scoped Topology BigOperators Classical ContDiff
variable {D j h :ℕ} {L : Side}(x : Site L)

def paper (D : ℕ) := trimmed Axis (D+1)
lemma paper_is (p: Seasons): p∈paper D ↔ upper p≤D:= by rw [paper,trim_def,Nat.lt_succ_iff]
abbrev Spring (D : ℕ) := ↥(paper D)
lemma paper_fits (p:Spring D): upper p.val≤D :=(paper_is _).mp p.property
def peers (D j:ℕ): Finset (Spring D):= Finset.univ.filter (fun u=>upper u.val=j)
lemma notch_le {q}(h:upper q≤D)(p:Studio D): ‖notch q h p‖≤‖p‖:=le_panel ..

lemma halo_cone (p q:Seasons)(k: Brush D)(h:word k=q) : (cone D p).val k origin=if q=p then 1 else 0:=by
    rw [← notched (p:=q) (by rw [←h,word_val]; exact Nat.le_of_lt_succ k.1.isLt) (cone D p) k h,notch_basis]

lemma lowered (f:Studio D) (q:ℕ)(hp:q≤D)(he : ∀ k:Brush D,q≤k.1.val→∀ v, ‖f.val k v‖≤0)(h : ∀ k:Brush D,k.1.val<q→f.val k origin=0):f=0:=norm_le_zero_iff.mp (by simpa using fog f q 0 hp le_rfl he h)
lemma expansion (f:Garden D)(j:ℕ)(h:j<D) : portrait D (dawn f j)=∑ i∈peers D j, notch i.val (paper_fits i) (portrait D f) • cone D i.val := by
    let T i := notch _ (paper_fits i) (portrait D f)
    rw [←sub_eq_zero]; apply lowered _ (j+1) h
    · intro k hv x; simp only [Submodule.coe_sub, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower, Pi.sub_apply, Finset.sum_apply,Pi.smul_apply,ContinuousMap.sub_apply,ContinuousMap.sum_apply]; change ‖iteratedFDeriv ℝ k.1.val (diagonal (coeff f.val j 0)) _ _- ∑ i∈peers D j, (T i • ((cone D i.val).val k) : C(Pier,ℝ)) x‖≤0
      have hh := hv
      rw [diag_free _ (coeff_symm (f:=f.val) (j:=j) (x:=0) (show ContDiffAt ℝ _ _ _ from (show ContDiff ℝ D f.val from f.property).contDiffAt.of_le (Nat.cast_le.mpr h.le))) hv]; simp only [_root_.zero_apply]; rw [Finset.sum_eq_zero, sub_self,norm_zero]; intro i hi
      have hp := (Finset.mem_filter.mp hi).2
      change T i * iteratedFDeriv ℝ k.1.val (rose i.val) x.val (basis ∘ k.2) = 0
      rw [rose_atom i.val k.2 (hp.trans_le (by omega)), if_neg (show granary k.2 ≠ i.val from fun he=>by have ht:= congr_arg upper he;rw [stocked,hp] at ht;omega), mul_zero]
    intro k hv; simp only [Submodule.coe_sub, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower,Pi.sub_apply, Finset.sum_apply, ContinuousMap.sub_apply,Pi.smul_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply]; simp_rw [halo_cone _ _ _ rfl]; rw [sub_eq_zero]; change halo (dawn f j) k 0=_
    rcases eq_or_ne k.1.val j with H|H
    · let K:Spring D:= ⟨word k,(paper_is _).mpr ((word_val k).trans_le (H.trans_le h.le))⟩
      rw [halo_done,Finset.sum_eq_single K];swap
      · intro l hl hn; rw [if_neg (show word k≠l.val from fun he=> hn ((Subtype.ext he.symm) )),smul_zero]
      swap; · intro hK; exact False.elim (hK (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(word_val k).trans H⟩))
      rw [if_pos rfl,smul_eq_mul,mul_one,notched _ _ k (by rfl)]; change _ = halo f k 0;rw [halo_done]; congr 2
      rw [H]; exact Free.coeff_diagonal _ (coeff_symm (f:=f.val) (j:=j) (x:=0) (show ContDiffAt ℝ _ _ _ from (show ContDiff ℝ D f.val from f.property).contDiffAt.of_le (Nat.cast_le.mpr h.le)))
    rw [Finset.sum_eq_zero,halo_done];swap
    · intro l hl; rw [if_neg (show word k ≠ l.val from fun he=> H (((word_val k).symm.trans (congr_arg upper he)).trans (Finset.mem_filter.mp hl).2)),smul_zero]
    change _ • coeff (Tensor.diagonal (coeff _ _ _)) _ _ _= _; rw [Free.coeff_diagonal_ne _ (coeff_symm (f:=f.val) (j:=j) (x:=0) (show ContDiffAt ℝ _ _ _ from (show ContDiff ℝ D f.val from f.property).contDiffAt.of_le (Nat.cast_le.mpr h.le))) H ]; simp

def pamphlet (p: Studio D)(j:ℕ) : Studio D:=∑ i∈peers D j,notch _ (paper_fits i) p • cone D i.val
lemma earns (p: Studio D)(q:ℕ)(hq:q≤ D)(hL : 2≤L.val) : ‖throughW x D hL p -∑ i∈Finset.range q,pamphlet (throughW x D hL p) i‖ ≤ 32^q*(scale L ^ q * ‖p‖) := by
   obtain ⟨f,rfl⟩:=portrayed D p; rw [through_show];
   have hh:=sunset_bill x f hL _ hq
   convert hh using 3
   rw [sunset,map_sub,map_sum]; congr 1
   exact Finset.sum_congr rfl fun i hi=> (expansion _ _ ((Finset.mem_range.mp hi).trans_le hq)).symm
lemma notch_pull (p: Seasons)(k: Seasons)(h:upper k≤D)(hL:2≤L.val)(he:upper p≤upper k) : notch k h (throughW x D hL (cone D p)) = scale L^upper k *(if k=p then 1 else 0):=by
    let b : Brush D:=finger h; have hb:word b=k:=(draw_any k h).choose_spec; have huv:= (word_val b).symm.trans (congr_arg upper hb)
    rw [notched h _ b hb,cone,through_show,berry _ _ _ _ hL]; change scale L^_*iteratedFDeriv ℝ _ (rose p) _ _= _
    rw [rose_atom p b.2 (huv.symm ▸ he)]; change _ * (if word b=_ then _ else _)=_; rw [hb,←huv]
lemma notch_down {p : Seasons}(h:upper p≤D)(T:Studio D)(hL:2 ≤ L.val):
     ‖notch p h (throughW x D hL T)‖ ≤ scale L ^ upper p * ‖T‖ := by
    obtain ⟨f,rfl⟩:= portrayed D T
    rw [through_show,notched h _ (finger h) (draw_any p h).choose_spec, berry _ _ _ _ hL,norm_mul,Real.norm_of_nonneg (pow_nonneg scale_pos.le _), ← word_val,show word (finger h)=_ from (draw_any p h).choose_spec];exact mul_le_mul_of_nonneg_left (le_panel ..) (pow_nonneg scale_pos.le _)
lemma flag_built {p: Seasons}(h: upper p<D)(hL:2≤L.val): throughW x D hL (cone D p)=∑ i∈Finset.range (upper p+1),pamphlet (throughW x D hL (cone D p)) i:= by
    let f:= bowl x (tint D p);
    have hx : throughW x D hL (cone D p)=portrait D f:= through_show ..
    rw [←sub_eq_zero,hx,show (∑ i∈Finset.range (upper p+1),pamphlet (portrait D f) i)=∑ i∈Finset.range (upper p+1),portrait D (dawn f i) from (Finset.sum_congr rfl fun i hi=> by
       have hh := Finset.mem_range.mp hi
       exact (expansion f i (by omega)).symm), ← map_sum, ← map_sub];
    apply lowered _ (upper p+1) h _ (sunset_low f _ · h)
    intro k hk u; rw [sunset_high _ _ k h hk]; unfold f; rw [berry _ _ _ _ hL]; change ‖_* iteratedFDeriv ℝ k.1.val (rose p) _ _‖ ≤ _; rw [rose_atom p k.2 (by omega),if_neg (show granary _ ≠p from fun he=>by have hv:=congr_arg upper he;rw [stocked] at hv;omega), mul_zero,norm_zero]
end YM.FormalBulk08.Dawn
