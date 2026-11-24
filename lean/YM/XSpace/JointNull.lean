import YM.XSpace.ProbeLine
/-! # Middle points null to both endpoints but not spectators -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.ProbeLine
open Set Filter Function MeasureTheory Maxwell Tensor
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
local notation "I" => Complex.I

lemma evade {α V W:Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [Nontrivial V]
    (f:α→V→ₗ[ℝ] W) (S:Finset α) : ∃ v:V, v ≠ 0 ∧ ∀ i∈ S,f i≠0→f i v≠0 := by
  have ht {X:Type} [AddCommGroup X] [Module ℝ X] (x y:X) (h:x≠0∨y≠0):∀ᶠ r:ℝ in atTop,x+r • y≠0:= by
    rcases eq_or_ne y 0 with hs|hs
    · rw [hs]; exact Eventually.of_forall fun r=>by simpa only [smul_zero,add_zero] using h.resolve_right (not_not.mpr hs)
    by_cases ht:∃ r:ℝ,x+r • y=0
    · obtain ⟨r,hr⟩:=ht; refine (eventually_gt_atTop r).mono fun s h=>?_ ; exact fun H=> h.ne (smul_left_injective ℝ hs (add_left_cancel (hr.trans H.symm)))
    exact Eventually.of_forall fun v h=> ht ⟨v,h⟩
  induction S using Finset.induction_on with
  | empty=> obtain ⟨v,h⟩:=exists_ne (0:V); exact ⟨v,h,fun i h=> False.elim (Finset.notMem_empty _ h)⟩
  | @insert i S h ih=>
    obtain ⟨v,hv,hP⟩:=ih
    by_cases he:f i=0
    · exact ⟨v,hv,fun k hk hq=> hP k ((Finset.mem_insert.mp hk).resolve_left (fun ht=> hq (ht ▸ he))) hq⟩
    obtain ⟨u,hu⟩:= not_forall_not.mp (fun h=>he (LinearMap.ext fun v=> not_not.mp (h v)))
    change f i u≠0 at hu
    have hh j (hx : j∈insert i S): ∀ᶠ r:ℝ in atTop,f j≠0→ f j (v+r • u)≠0 := by
      by_cases hg:f j=0; · simp [hg]
      have hh: f j v≠0 ∨ f j u ≠0:= (Finset.mem_insert.mp hx).elim (fun he=>he ▸ Or.inr hu) (fun hp=>Or.inl (hP j hp hg))
      exact (ht _ _ hh).mono fun r hr _=> by simpa using hr
    obtain ⟨r,H,hr⟩:= ((ht v u (Or.inl hv)).and ((eventually_all_finset (insert i S)).mpr hh)).exists; exact ⟨_,H,hr⟩

lemma cubic_id (m u y:E4): cubic m u y=(↑(‖m-y‖^2-‖u‖^2):ℂ)+I*2* ↑(inner ℝ (m-y) u) := by
  unfold cubic; simp only [EuclideanSpace.real_norm_sq_eq,← Finset.sum_sub_distrib,Free.inner4,Complex.ofReal_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; simp [corner,Complex.ext_iff, Complex.mul_re,Complex.mul_im]; simp [sq, Complex.mul_re, Complex.mul_im]; ring

structure Congruent (X:Set E4)(m v u:E4):Prop where
  real : v≠0
  orth : inner ℝ v u=0
  normy: ‖u‖=‖v‖
  regular : ∀ x∈X,cubic m u x≠0
lemma joint (X:Finset E4) (m v:E4) (hv:v≠0)(h₁:m+v∉X)(h₂:m-v∉X): ∃ u:E4,Congruent X m v u:= by
  let V:= Submodule.span ℝ {v}; let Y:= Vᗮ
  have he : Module.finrank ℝ V+Module.finrank ℝ Y=4 := Submodule.finrank_add_finrank_orthogonal V|>.trans (by simp [E4])
  rw [show Module.finrank ℝ V=1 from finrank_span_singleton hv] at he
  haveI : Nontrivial Y:= Module.nontrivial_of_finrank_pos (R:=ℝ) (by omega : 0<Module.finrank ℝ Y)
  let f x : Y→ₗ[ℝ] ℝ := (innerSL ℝ (m-x)).toLinearMap.comp Y.subtype
  obtain ⟨p,hp,H⟩:= evade f X
  let r:= ‖v‖/‖p‖; let u:= r • p.val
  have hx:=norm_pos_iff.mpr hv; have hy:=norm_pos_iff.mpr hp; have hr:0<r:=div_pos hx hy
  have ht : ‖u‖=‖v‖:= by unfold u; rw [norm_smul,Real.norm_of_nonneg hr.le,show ‖p.val‖=‖p‖ from rfl]; exact div_mul_cancel₀ _ hy.ne'
  refine ⟨u,hv,Submodule.mem_orthogonal_singleton_iff_inner_right.mp (Y.smul_mem r p.property),ht, fun x hg h=>?_⟩
  rw [cubic_id, ht] at h
  have ha := congr_arg Complex.re h; have hl := congr_arg Complex.im h
  simp [Complex.mul_re,Complex.mul_im,sq] at ha hl
  have he : ‖m-x‖=‖v‖:=by nlinarith [norm_nonneg (m-x)]
  have hh : f x =0:= by
    by_contra he'
    apply H x hg he'; change inner ℝ (m-x) p.val=0; simpa [u,inner_smul_right,hr.ne'] using hl
  have hX : m-x∈V := by
    rw [← Submodule.orthogonal_orthogonal V]
    apply (Y.mem_orthogonal' _).mpr; intro i hi
    exact LinearMap.congr_fun hh (⟨i,hi⟩:Y)
  obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp hX
  rw [← hc,norm_smul] at he; rw [Real.norm_eq_abs] at he
  by_cases h:0≤c
  · rw [abs_of_nonneg h] at he; rw [show c=1 by nlinarith,one_smul] at hc
    apply h₂; exact (show x=m-v by rw [hc]; abel) ▸ hg
  rw [abs_of_neg (lt_of_not_ge h)] at he; rw [show c= -1 by nlinarith,neg_one_smul] at hc
  apply h₁; exact (show x=m+v by rw [neg_eq_iff_eq_neg.mp hc]; abel) ▸ hg
namespace Congruent
variable {x y m u v:E4} {X:Set E4} (h:Congruent X m v u)
include h
lemma raw: u≠0 := norm_pos_iff.mp (h.normy.symm ▸ norm_pos_iff.mpr h.real)
lemma null_one: cubic m u (m+v)=0:= by rw [cubic_id,show m-(m+v)= -v by abel]; simp [h.normy,inner_neg_left,h.orth]
lemma null_two: cubic m u (m-v)=0:= by rw [cubic_id]; simp [h.normy,h.orth]
lemma twins (t:ℝ): rsq (drifts m u (m+v) t)=rsq (drifts m u (m-v) t):= by
  unfold rsq drifts
  rw [show m+t • u-(m+v)= t • u+ -v by abel,show m+t • u-(m-v)=t • u+v by abel]
  simp only [← real_inner_self_eq_norm_sq, inner_add_left,inner_add_right, inner_neg_right,inner_neg_left, inner_smul_left, inner_smul_right, h.orth,show inner ℝ u v=0 by rw [real_inner_comm,h.orth]]; ring
end Congruent
end YM.XSpace.ProbeLine
