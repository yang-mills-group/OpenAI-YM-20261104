import YM.MSbar.Pole.Dimension.Even

/-! # Dimension shift estimates -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical Interval
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E} {f : ℝ × E→ℂ} {p q : Price E}
variable (o : IsOpen U) (hc : ContinuousOn p.val U)
  (h : Packet (univ ×ˢ U) (p.back Prod.snd) (Moment q) f)
local notation "Π₀" => Ioc (0:ℝ) 1
local notation "ω" => volume.restrict Π₀

private def shift (t : ℝ) : ℝ × E →L[ℝ] ℝ × E := (t • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)
private lemma shifted (t : ℝ) (x : ℝ × E) : shift t x = (t*x.1,x.2) := rfl

include o hc h
/-- Cap integral also good on wider bounded radial windows. -/
lemma cap (R : ℝ) (hR : 0≤R) :
    Barrel ω (Ioo (-R) R ×ˢ U) (p.back Prod.snd) (Moment q) (fun t x => f (shift t x)) := by
  let C := ‖@shift E _ _ 0‖+‖ContinuousLinearMap.fst ℝ ℝ E‖+R+2
  have hm : R+1 ≤ C := by unfold C; linarith [norm_nonneg (@shift E _ _ 0),norm_nonneg (ContinuousLinearMap.fst ℝ ℝ E)]
  have hC : 1 ≤ C := by linarith
  let g t (x : ℝ × E) := f ((fun _=> (0:ℝ × E)) t + shift t x)
  have ht : Barrel ω (Ioo (-R) R ×ˢ U) (p.back Prod.snd) (Moment q) g := by
    apply pullBarrel shift (T:=fun _ : ℝ => (0:ℝ × E)) h (isOpen_Ioo.prod o)
      (p:=p.back Prod.snd) (q:=Moment q) (hc.comp (continuousOn_snd) fun x hx => hx.2) (C:=C) (zero_le_one.trans hC)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ⟨hz,ht⟩
      apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hC)
      intro x
      rw [shifted]; change max ‖t*x.1‖ ‖x.2‖ ≤ C*‖x‖; refine max_le ?_ ?_
      · rw [norm_mul,Real.norm_of_nonneg hz.le]; exact mul_le_mul ((ht.trans hC)) (norm_fst_le _) (norm_nonneg _) (zero_le_one.trans hC)
      exact (norm_snd_le _).trans (le_mul_of_one_le_left (norm_nonneg _) hC)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x hx
      obtain ⟨hxU,hxV⟩ := mem_prod.mp hx
      simp only [zero_add,shifted]
      refine ⟨mem_prod.mpr ⟨mem_univ _,hxV⟩,?_,?_⟩
      · exact (le_mul_of_one_le_left (p.pos _).le hC : p x.2 ≤ C*p x.2)
      have ha : 1+|x.1| ≤ C*(1+|t*x.1|) := by
        refine le_trans ((show 1+|x.1|≤R+1 from by linarith [(abs_lt.mpr (show -R < x.1 ∧ x.1 < R from hxU))]).trans hm) ?_
        exact le_mul_of_one_le_right (zero_le_one.trans hC) (by simpa only [le_add_iff_nonneg_right] using (abs_nonneg (t*x.1))) 
      change (1+|x.1|)*q x.2≤C*((1+|t*x.1|)*q x.2); rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ha (q.pos _).le
    · intro x hx
      suffices Continuous (fun t : ℝ => g t x) from this.aestronglyMeasurable
      simp only [g,zero_add,shifted]
      refine continuous_iff_continuousAt.mpr fun i => (h.smooth (shift i x) (mem_prod.mpr ⟨mem_univ _,hx.2⟩)).continuousAt.comp (f:=fun t : ℝ => (t*x.1,x.2)) (x:=i)
        (show Continuous (fun t : ℝ => (t*x.1,x.2)) from by fun_prop).continuousAt
  simpa only [g,zero_add] using ht

omit hc in
lemma cap_eq (R : ℝ) : ∀ x∈(Ioo (-R) R ×ˢ U),
    higher f =ᶠ[nhds x] fun y => -(2:ℝ)⁻¹ • ∫ t, letter (letter f) (shift t y) ∂ω := by
  intro x hx
  filter_upwards [(isOpen_Ioo.prod o).mem_nhds hx] with y hy
  conv_rhs => simp only [shifted]; rw [← intervalIntegral.integral_of_le (f:=fun t : ℝ=> letter (letter f) (t*y.1,y.2)) zero_le_one]
  exact alternative h (mem_prod.mp hy).2 y.1

variable [FiniteDimensional ℝ E]
lemma nearer (R : ℝ) (hR : 0 ≤ R) : Packet (Ioo (-R) R ×ˢ U) (p.back Prod.snd) (Moment q) (higher f) := by
  let X := (-(2:ℝ)⁻¹) • ContinuousLinearMap.id ℝ ℂ
  exact (Packet.apply (X:=X) (cap o hc (through_letter (through_letter h)) R hR).integrates).congr (cap_eq o h R)
omit o hc h [FiniteDimensional ℝ E] in
private lemma inverse_slow {x : ℝ} (hs : 1≤|x|) (n:ℕ) : ‖iteratedFDeriv ℝ n (fun y : ℝ => y⁻¹) x‖ ≤ (n.factorial:ℝ) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,iter_deriv_inv]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_zpow]
  rw [Real.norm_natCast]; refine mul_le_of_le_one_right (by positivity) ?_
  exact le_trans (zpow_le_zpow_right₀ hs (show -(1:ℤ) - n ≤ 0 by omega)) (le_of_eq (zpow_zero _))
omit hc [FiniteDimensional ℝ E] in
lemma farther (he : EvenOn U f) : Packet (({r : ℝ | 1 < abs r}) ×ˢ U) (p.back Prod.snd) (Moment q) (higher f) := by
  let S := {r : ℝ | 1 < abs r}; let T := S ×ˢ U; let Y : ℝ × E→ℝ := fun x=>x.1⁻¹
  have ho : IsOpen T := (isOpen_lt continuous_const continuous_abs).prod o
  let D : ℝ × E →L[ℝ] ℝ := ContinuousLinearMap.fst ..
  have hh (x : ℝ×E) (hx : x∈T) : x.1 ≠ 0 := abs_pos.mp (zero_lt_one.trans hx.1)
  have hY : Packet T (p.back Prod.snd) 1 Y := by
    have Hx (x : ℝ × E) (hx : x∈T) : ContDiffAt ℝ ∞ Inv.inv x.1 := contDiffAt_id.inv (hh x hx)
    refine ⟨fun x hx => (Hx x hx).comp x D.contDiff.contDiffAt,fun i j => ⟨(i.factorial:ℝ) * ‖D‖^i,0,by positivity,fun x hx => ?_⟩⟩
    simp only [Price.one_apply,one_pow,mul_one,pow_zero]
    apply le_trans _ (mul_le_mul_of_nonneg_right (inverse_slow hx.1.le i) (show 0 ≤ ‖D‖^i by positivity))
    have hf : ContDiffAt ℝ i Inv.inv ((0:ℝ)+D x) := by rw [zero_add]; exact (Hx x hx).of_le (by exact_mod_cast (show (↑i:ℕ∞)≤⊤ from le_top))
    have hh' := iter_affine_le D 0 x i hf
    simp only [zero_add] at hh'; exact hh'
  let C := -(2:ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℂ
  have ht := (through_letter h).mono (show T ⊆ _ from fun x hx => ⟨mem_univ _,hx.2⟩)
  exact ((ht.apply (X:=C)).bilinear hY (ContinuousLinearMap.lsmul ℝ ℝ).flip).congr (fun x hx =>
    mem_of_superset (ho.mem_nhds hx) (fun y hy => alt_of_ne h he (hh y hy) hy.2))
include o hc h
lemma smooth (he : EvenOn U f) : Packet (univ ×ˢ U) (p.back Prod.snd) (Moment q) (higher f) := by
  refine ((nearer o hc h 2 zero_le_two).union (farther o h he)).mono (fun x ⟨_,hx⟩ => ?_)
  rcases lt_or_ge 1 |x.1| with hh|hh
  · exact Or.inr ⟨hh,hx⟩
  exact Or.inl ⟨abs_lt.mp (hh.trans_lt one_lt_two),hx⟩
lemma keeps_cr {v w : E} (hh : ∀ x∈univ ×ˢ U,CR ((0:ℝ),v) (0,w) f x) : ∀ x∈univ ×ˢ U,
    CR ((0:ℝ),v) (0,w) (higher f) x := by
  let V : ℝ × E := (0,v); let W : ℝ × E := (0,w)
  have hm := through_letter (through_letter h)
  let g := letter (letter f)
  have hp x (hx : x∈ univ ×ˢ U) : CR V W g x := field_cr (isOpen_univ.prod o) (through_letter h)
    (fun i hi => field_cr (isOpen_univ.prod o) h hh _ hi) _ hx
  intro x hx; let R := |x.1|+1; have hR : 0 ≤ R := by dsimp [R]; positivity
  have hx' : x ∈ Ioo (-R) R ×ˢ U := ⟨abs_lt.mp (lt_add_one _),hx.2⟩
  let H (y : ℝ×E) : ℂ := ∫ t,g (shift t y) ∂ω
  have hH := cap o hc hm R hR
  have hv : CR V W H x := by
    apply integral_cr hH hx' -- arguments
    filter_upwards with t
    have hx'' : shift t x ∈ univ ×ˢ U := ⟨mem_univ _,hx.2⟩
    have he : fderiv ℝ (fun y => g (shift t y)) x=(fderiv ℝ g (shift t x)).comp (shift t) :=
      (((hm.smooth (shift t x) hx'').differentiableAt (by simp)).hasFDerivAt.comp x (shift (E:=E) t).hasFDerivAt).fderiv
    change CR V W (fun y => g (shift t y)) x; unfold CR
    rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,show shift t W=W by simp [W,shifted],show shift t V=V by simp [V,shifted] ]
    exact hp (shift t x) hx''
  let c := -(2:ℝ)⁻¹
  have ha : fderiv ℝ (higher f) x = c • fderiv ℝ H x := by
    apply ((show DifferentiableAt ℝ H x from (hH.exchange hx').differentiableAt).hasFDerivAt.const_smul c|>.congr_of_eventuallyEq ?_).fderiv
    exact cap_eq o h R x hx'
  change fderiv ℝ (higher f) x W = Complex.I*fderiv ℝ (higher f) x V
  rw [ha]; change c • (fderiv ℝ H x W)=Complex.I*(c • (fderiv ℝ H x V)); rw [show fderiv ℝ H x W=_ from hv,mul_smul_comm]
end YM.MSbar.Pole.Radial
