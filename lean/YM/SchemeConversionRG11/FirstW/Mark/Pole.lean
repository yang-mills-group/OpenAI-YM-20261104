import YM.SchemeConversionRG11.FirstW.Kernel.Outcrop
import YM.Pert.First.Completion
/-! Direct (& odd-lifted) torus covariance as probes, escape of torus gradients. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Pert.Align Topology Maxwell
open scoped BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {X : Type*}
abbrev Wind (G : Gauge) (X : Type*) := Lattice.Links X G.Color
abbrev FullT (G : Gauge) (n : Side) := Wind G (Per n)
abbrev Ear (G : Gauge) (X : Type*) := Module.Dual ℝ (Wind G X)
-- probe tested by inner rather than coordinates. tiltPinches is a dual-linear map.
def pinch (e : Edge (Four X)) (u : G.Color) : Ear G X := (innerSL ℝ u).toLinearMap ∘ₗ LinearMap.proj e
@[simp] lemma pinch_eq (e : Edge (Four X)) (u : G.Color) (A : Wind G X) : pinch e u A = inner ℝ u (A e) := rfl
def needle (e : Edge (Site n)) (u : G.Color) : FullT G n := Pi.single e u
lemma pinched (x y : Edge (Site n)) (u : G.Color) : needle x u y = if y=x then u else 0 := by by_cases h : y=x <;> simp [needle,h]
lemma unit_hit (u v : G.ColorIndex) : inner ℝ (unitColor G u) (unitColor G v) = if v=u then 1 else 0 := by rw [to_color,unitPaint]
lemma inkSum (u : G.Color) : u = ∑ v:G.ColorIndex, inner ℝ (unitColor G v) u • unitColor G v := by
  ext t; simp only [WithLp.ofLp_sum, Finset.sum_apply,PiLp.smul_apply,unitPaint]
  rw [Finset.sum_eq_single t]; swap; · exact fun b _ h=>by rw [if_neg (Ne.symm h),smul_zero]
  · rw [if_pos rfl,smul_eq_mul,mul_one,real_inner_comm,to_color]
  simp
lemma ink_eq {u v : G.Color} (h : ∀ t:G.ColorIndex, inner ℝ (unitColor G t) u=inner ℝ (unitColor G t) v) : u=v := by nth_rw 1 [inkSum u,inkSum v]; simp_rw [h]
lemma ink_zero {u : G.Color} (h : ∀ t:G.ColorIndex, inner ℝ (unitColor G t) u=0) : u=0 := ink_eq fun t => by rw [h,inner_zero_right]
def ladder (p : Ear G (Per n)) : FullT G n := fun e=> ∑ t:G.ColorIndex,p (needle e (unitColor G t)) • unitColor G t
lemma ladder_val (p : Ear G (Per n)) (e : Edge (Site n)) (u : G.Color) : inner ℝ u (ladder p e) = p (needle e u) := by
  rw [ladder,inner_sum]
  nth_rw 2 [inkSum u]
  rw [show needle e (∑ v, _)=∑ v:G.ColorIndex,(inner ℝ (unitColor G v) u) • (needle e (unitColor G v)) from funext fun t=> by simp only [pinched, Finset.sum_apply,Pi.smul_apply]; split_ifs <;> simp,map_sum]
  apply Finset.sum_congr rfl;intro x _; rw [p.map_smul,real_inner_smul_right,real_inner_comm,smul_eq_mul,mul_comm]
lemma ladder_sol (p : Ear G (Per n)) (A : FullT G n) : (∑ l,inner ℝ (A l) (ladder p l)) = p A := by
  simp_rw [ladder_val,← map_sum,show (∑ l,needle l (A l)) = A from funext (fun t => by rw [Finset.sum_apply]; simp only [pinched];simp)]

def tbranch (G : Gauge) (n : Side) : Ear G (Per n) →ₗ[ℝ] FullT G n where
  toFun p := fun e=> ∑ t:G.ColorIndex, (p (Orb.ghostLink e (unitColor G t))) • unitColor G t
  map_add' p q := by ext1 e; simp [add_smul,Finset.sum_add_distrib]
  map_smul' c p := by ext1 e; simp [Finset.smul_sum,smul_smul]
lemma branch_elem (p : Ear G (Per n)) (e) (u : G.Color) : inner ℝ u (tbranch G n p e) = p (Orb.ghostLink e u) := by
  change inner ℝ _ (∑ t:G.ColorIndex, p (Orb.ghostLink e (unitColor G t)) • unitColor G t) = _
  rw [inner_sum]
  nth_rw 2 [inkSum u]
  rw [show Orb.ghostLink e (∑ v, _)=∑ v:G.ColorIndex,(inner ℝ (unitColor G v) u) • (Orb.ghostLink e (unitColor G v)) from funext fun t=> by rw [Finset.sum_apply]; simp only [Orb.ghostLink,Pi.smul_apply]; split_ifs with h <;> simp [Finset.smul_sum,smul_comm _ (inner ℝ (unitColor G _) u)],map_sum]
  apply Finset.sum_congr rfl;intro x _; rw [p.map_smul,real_inner_smul_right,real_inner_comm,smul_eq_mul,mul_comm]
lemma branch_at (e : Edge (Site n)) (u : G.Color) : tbranch G n (pinch e u)=Orb.ghostLink e u := by
  funext s; apply ink_eq; intro t; rw [branch_elem,pinch_eq]; unfold Orb.ghostLink; by_cases h : e.2=s.2
  · rw [if_pos h,if_pos h.symm,real_inner_smul_right,real_inner_smul_right, ← neg_sub s.1 e.1,Full.toroid_even,real_inner_comm]
  rw [if_neg h,if_neg (Ne.symm h),inner_zero_right,inner_zero_right]
lemma pips_all (p : Ear G (Per n)) : p = ∑ e:Edge (Site n), pinch e (ladder p e) := by
  apply LinearMap.ext; intro A
  simp only [LinearMap.sum_apply,pinch_eq]; rw [←ladder_sol p A]; exact Finset.sum_congr rfl (fun i _=>real_inner_comm ..)
lemma branch_masses (p q : Ear G (Per n)) : p (tbranch G n q) = q (tbranch G n p) := by
  nth_rw 1 [pips_all p]; conv_rhs => arg 2; rw [pips_all p]
  simp only [LinearMap.sum_apply,pinch_eq,branch_elem,map_sum,branch_at]
end YM.RG11.FirstW
