import YM.Comparison.Density.Mirrors.Track
import YM.Comparison.Density.Mirrors.Difference
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Residual

/-!
# Re-expression of the scalar vacuum log after aligning its hull

Exact translated equality with explicit pointwise signed partner on the
ORIGINAL domain. Aggregating a translation-summed jet with masks still on
different terms need not give the jet estimate one would consume. This is
one of the align-and-attach operations that will be used on the marker
polynomial (before dividing any marked forced bill). All read supports are
in actual lattice units.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Mirrors
open Function Lattice Wilson RG MeasureTheory Finset AnalyticBridge.VerifiedReset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side} (p : BudgetPoint) (f : Links ℤ G.El → ℝ)

lemma neighborhood_incl {k l : ℕ} {x y : Site n} (h : separation y x + k ≤ l) :
    neighborhood k x ⊆ neighborhood l y := by
  intro z hz; apply (neighborhood_iff ..).2
  exact (separation_triangle y x z).trans ((Nat.add_le_add_left ((neighborhood_iff ..).1 hz) _).trans h)
lemma neighborhood_mono {k l : ℕ} {x : Site n} (h : k≤l) : neighborhood k x ⊆ neighborhood l x :=
  neighborhood_incl (by simpa using h)
lemma neighborhood_signed (b : ℕ) (x u : Site n) (s : Signed) :
    neighborhood b (affine s u x)=(neighborhood b x).image (affine s u) := by
  have he : Injective (affine s u) := fun y z k=> s.act_injective (add_right_cancel k)
  ext y; obtain ⟨y,rfl⟩:= Finite.surjective_of_injective he y
  simp [neighborhood_iff,affine,s.act_injective.eq_iff]

def test (f : Links ℤ G.El→ ℝ) (k : Side) (o : Site n) (x : Site (quad k)) (U : Config G n) :=
  f (expandAt x (tiled k o U))

lemma test_signed (k : Side) (s : Signed) (u o : Site n) (x : Site (quad k))
    (h : ∀ U s,f (pull s 0 U)=f U) (U : Config G n) :
    test f k o x (pull s u U) = test f k (affine s u o) (s.act x) U := by
  unfold test tiled; rw [expandAt_pull, field_signed, expandAt_pull,h, affine, add_zero]

lemma test_gauge (h : GaugeInvariant f) (k : Side) (o : Site n) (x : Site (quad k)) :
    GaugeInvariant (test f k o x) := by
  intro c U; unfold test tiled; rw [expandAt_gauge,field_gauge,expandAt_gauge,h]

lemma test_meas (h : Measurable f) (k : Side) (o : Site n) (x : Site (quad k)) :
    Measurable (test f k o x) := h.comp (show Continuous (fun U : Config G n=> expandAt x (tiled k o U)) from by
      apply Continuous.comp (g:=expandAt x); swap; exact tiled_cont ..
      unfold expandAt; fun_prop).measurable

lemma test_local (k : Side) (o : Site n) (x : Site (quad k)) :
    LocalOn (neighborhood k.val o) (test f k o x) := fun U V hh=>
  congrArg (fun W=>f (expandAt x W)) (tiled_local k o U V hh)

def weightAt (k : Side) (o : Site n) (U : Config G n) : ℝ := ∑ x, test f k o x U

def restored (k : Side) (o : Site n) : Config G n→ℝ := ∑ j : Fin 5, multiplier j • weightAt f (advance k j) o

def maskCost (r : ℕ) (o : Site n) : Config G n→ℝ := masked p.threshold (neighborhood r o) (f ∘ expandAt o)

def maskGain (k : Side) (d : ℕ) (o : Site n) := masked p.threshold (neighborhood d o) (restored f k o)

def shifted (k : Side) (o : Site n) (x : Site (quad k)) : Site n := o-wrap n (reflectAt k x)

lemma shift_signed (k : Side) (o u : Site n) (x : Site (quad k)) (s : Signed) :
    shifted k (affine s u o) (s.act x)= affine s u (shifted k o x) := by
  unfold shifted affine; rw [reflectAt_signed,Signed.act_sub,wrap_signed]; abel

lemma shift_sep (k : Side) (o : Site n) (x : Site (quad k)) : separation o (shifted k o x)≤k.val := by
  rw [separation_comm]
  exact (by simpa only [site_track, shifted, add_sub_cancel] using track_sites k (shifted k o x) x)

/-- Re-indexed sum, with the actual transformed mask (not one at the new centre). -/
def joint (k : Side) (d : ℕ) (o : Site n) (U : Config G n) :=
  ∑ j : Fin 5, multiplier j * ∑ x,
    let s := advance k j
    let w := shifted s o x
    masked p.threshold (neighborhood d w) (test f s w x) U

/-- Positive sign here means old minus re-expressed terms. -/
def flagLog (r : ℕ) (k : Side) (d : ℕ) (o : Site n) := maskCost p f r o - joint p f k d o

lemma restored_value (k : Side) (o : Site n) (U : Config G n) :
    restored f k o U= ∑ j : Fin 5, multiplier j * ∑ x, test f (advance k j) o x U := by
  simp [restored,Finset.sum_apply,weightAt]

lemma cost_agreement (r : Side) (k : Side) (he : r.val ≤ k.val) (d : ℕ) (o : Site n)
    (hm : k.val+4≤d) (U : Config G n)
    (hS : ∀ U s, f (pull s 0 U)=f U) (h : LocalOn (Lattice.box r.val) f) (hu : Healthy p.threshold (neighborhood (2*d) o) U) :
    flagLog p f r.val k d o U=0 := by
  have hi (j) : (advance k j).val ≤ d := by change k.val+j.val≤d; have hh:=j.isLt; omega
  have hb (j) (y : Site (quad (advance k j))) :
      Healthy p.threshold (neighborhood d (shifted (advance k j) o y)) U := by
    have ht:= shift_sep (advance k j) o y |>.trans (hi j)
    exact Finset.disjoint_of_subset_left (neighborhood_incl (by omega)) hu
  simp_rw [flagLog,Pi.sub_apply,joint, maskCost,
    masked_eq _ _ _ _ (Finset.disjoint_of_subset_left (neighborhood_mono (show r.val≤2*d by omega)) hu),
    masked_eq _ _ _ _ (hb _ _)]
  have he' j (x : Site (quad (advance k j))) :
      test f (advance k j) (shifted (advance k j) o x) x U= f (profile (sky r (advance k j) x) (expandAt o U)) := by
    unfold test tiled
    rw [evaluate_profile f r (advance k j) (he.trans (Nat.le_add_right ..)) hS h]
    congr 2
    funext ⟨a,i⟩; unfold Lattice.translate expandAt shifted; rw [map_add]; simp
  simp_rw [he']
  have ht:= eliminated r k he (fun s=> f (profile s (expandAt o U)))
  simp only [Function.comp_apply,sub_eq_zero]
  simpa only [profile_clear] using ht.symm

lemma paid (k : Side) (d : ℕ) (U : Config G n) :
    ∑ o, maskGain p f k d o U=∑ o, joint p f k d o U := by
  have he o : maskGain p f k d o U=∑ j : Fin 5, multiplier j *
      ∑ x, masked p.threshold (neighborhood d o) (test f (advance k j) o x) U := by
    unfold maskGain
    by_cases h : Healthy p.threshold (neighborhood d o) U <;> simp [h,restored_value]
  unfold joint; dsimp only
  simp_rw [he]; rw [sum_comm]; conv_rhs => rw [sum_comm]
  apply sum_congr rfl; intro i _
  rw [←mul_sum,←mul_sum]; apply congr_arg
  rw [sum_comm]; conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun j _=> ?_
  symm
  exact Equiv.sum_comp (Equiv.subRight (wrap n (reflectAt _ j))) (fun o=>masked p.threshold (neighborhood d o) (test f _ o j) U)

theorem accounted (r k d) (U : Config G n) :
    ∑ o, maskCost p f r o U=(∑ o, maskGain p f k d o U)+∑ o, flagLog p f r k d o U := by
  rw [paid]; simp [flagLog,sum_sub_distrib]

lemma weight_local (k : Side) (o : Site n) : LocalOn (neighborhood k.val o) (weightAt f k o) :=
  fun _ _ h => sum_congr rfl fun x _ => test_local f k o x _ _ h

lemma weight_gauge (h : GaugeInvariant f) (k : Side) (o : Site n) : GaugeInvariant (weightAt f k o) :=
  fun _ _=> sum_congr rfl fun x _=> test_gauge f h k o x _ _

lemma weight_borel (k : Side) (o : Site n) (h : Measurable f) : Measurable (weightAt f k o) := by
  unfold weightAt; exact Finset.measurable_fun_sum _ fun x _=>test_meas f h _ _ x

lemma restored_signed (k : Side) (o u : Site n) (s : Signed) (h : ∀ U s,f (pull s 0 U)=f U)
    (U : Config G n) : restored f k o (pull s u U)= restored f k (affine s u o) U := by
  simp_rw [restored_value,test_signed _ _ _ _ _ _ h]
  apply sum_congr rfl; intro i _; apply congr_arg
  exact Equiv.sum_comp s.actEquiv.toEquiv (fun x => test f _ _ x U)

lemma masked_signed {A : Support n} {F H : Config G n → ℝ} (t : ℝ) (x : Site n) (s : Signed)
    (U : Config G n) (h : H U= F (pull s x U)) :
    masked t (A.image (affine s x)) H U = masked t A F (pull s x U) := by
  by_cases he : Healthy t (A.image (affine s x)) U
  · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ ((healthy_image ..).1 he)]; exact h
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ fun H=>he ((healthy_image ..).2 H)]

lemma joint_signed (k : Side) (d : ℕ) (o u : Site n) (s : Signed)
    (h : ∀ U s, f (pull s 0 U)=f U) (U : Config G n) :
    joint p f k d (affine s u o) U=joint p f k d o (pull s u U) := by
  unfold joint; refine sum_congr rfl fun i _=> ?_; apply congr_arg; dsimp only
  rw [← Equiv.sum_comp s.actEquiv.toEquiv]
  refine sum_congr rfl fun x _=> ?_
  change masked p.threshold (neighborhood d (shifted _ _ (s.act x))) (test f _ (shifted _ _ (s.act x)) (s.act x)) U=_
  rw [shift_signed,neighborhood_signed]
  exact masked_signed _ _ _ _ (test_signed _ _ _ _ _ _ h U).symm

lemma flag_moves (r k d) (o u : Site n) (s : Signed) (h : ∀ U s, f (pull s 0 U)=f U) (U : Config G n) :
    flagLog p f r k d (affine s u o) U=flagLog p f r k d o (pull s u U) := by
  unfold flagLog; simp only [Pi.sub_apply,joint_signed p f k d _ _ s h]
  unfold maskCost; rw [neighborhood_signed]; apply congr_arg (fun a:ℝ=>a-joint p f k d o (pull s u U)); apply masked_signed
  rw [Function.comp_apply,Function.comp_apply,expandAt_pull,h]

lemma local_expand (r : ℕ) (o : Site n) (h : LocalOn (Lattice.box r) f) : LocalOn (neighborhood r o) (f ∘ expandAt o) := by
  refine fun U V hu=> LocalOn.expandAt (Lattice.box r) f h o U V (agrees_mono hu ?_)
  rintro _ ⟨p,hp,rfl⟩; exact (neighborhood_iff ..).2 (Work.E08.separation_box_add o (show p∈Lattice.box r from hp))

lemma masked_reads {X : Type*} [Zero X] {A : Support n} {F : Config G n→ X} (h : LocalOn A F) :
    UsesFinal p.threshold A (masked p.threshold A F) := by
  intro U V ha hh
  have hu := healthy_reads p.threshold A A (Finset.Subset.refl _) U V ha hh
  by_cases he : Healthy p.threshold A U
  · rw [masked_eq _ _ _ _ he, masked_eq _ _ _ _ (hu ▸ he)]; exact h U V ha
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (hu ▸ he)]

lemma flag_reads (r : Side) (k : Side) (d : ℕ) (h : LocalOn (Lattice.box r.val) f) (hm : r.val≤ k.val) (ht : k.val+4≤d) (o : Site n) :
    UsesFinal p.threshold (neighborhood (2*d) o) (flagLog p f r.val k d o) := by
  intro U V ha hh; unfold flagLog; simp only [Pi.sub_apply]; refine congrArg₂ (· - ·) ?_ ?_
  · exact Work.H03.reads_larger (neighborhood_mono (show r.val≤ 2*d by omega))
      (masked_reads p (local_expand f _ o h)) U V ha hh
  unfold joint
  refine sum_congr rfl fun i _=> congr_arg _ (sum_congr rfl fun y _=> ?_)
  have h₀ : (advance k i).val≤d := by change k.val+i.val≤d; have hi:=i.isLt; omega
  exact Work.H03.reads_larger (neighborhood_incl (show separation o (shifted (advance k i) o y)+d ≤2*d by
    have he:= shift_sep _ o y |>.trans h₀; omega))
    (masked_reads p (fun U V hu=> test_local f _ _ y U V (agrees_mono hu (Finset.coe_subset.mpr (neighborhood_mono h₀))))) U V ha hh

lemma masked_gauge {X : Type*} [Zero X] (t : ℝ) (A : Support n) (F : Config G n→ X) (h : GaugeInvariant F) :
    GaugeInvariant (masked t A F) := by
  intro z U
  have ht : Healthy t A (gauge z U)=Healthy t A U := by unfold Healthy; rw [gauge_flags]
  by_cases he : Healthy t A U <;> simp [he, ht, h z U]

lemma flag_gauge (r k d) (h : GaugeInvariant f) (o : Site n) : GaugeInvariant (flagLog p f r k d o) := by
  intro z U; unfold flagLog; simp only [Pi.sub_apply]; refine congrArg₂ (· - ·) ?_ ?_
  · exact masked_gauge _ _ (f ∘ expandAt o) (fun z U=> by rw [Function.comp_apply,expandAt_gauge,h]; rfl) z U
  unfold joint; refine sum_congr rfl fun i _=> ?_; apply congr_arg; dsimp only
  exact sum_congr rfl fun y _=> masked_gauge _ _ _ (test_gauge f h _ _ y) z U

lemma flag_borel (r k d) (h : Measurable f) (o : Site n) : Measurable (flagLog p f r k d o) := by
  apply Measurable.sub
  · apply masked_measurable; apply h.comp
    exact (show Continuous (expandAt o (K:=G.El)) from by unfold expandAt;fun_prop).measurable
  unfold joint; apply Finset.measurable_fun_sum; intro i _; apply Measurable.const_mul
  exact Finset.measurable_fun_sum _ fun y _=> masked_measurable _ _ _ (test_meas f h _ _ y)
end YM.Comparison.Density.Mirrors
