import YM.Next.MAXWELL.Flavor
import YM.Next.MAXWELL.Faint
import YM.Planned.ATOM_REGULAR_ESTIMATE.Degree

/-!
# Kelvin numerator of the curvature leg. Rational algebra preliminaries

We'll continue *just* one separation variable in a Wick correlation, with no interacter
coefficients. Evaluation at complex positions never used to define physical quantities. Retain the
Taylor-factorial conventions in `Probe`/`Flavor`.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Set MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace

abbrev Space := Axis → ℂ
abbrev Script := MvPolynomial Axis ℂ

def paint (x : E4) : Space := fun i ↦ (x i:ℂ)

def dot (x y : Space) := ∑ i, x i*y i

def sq (x : Space) := dot x x

def chart : Script := ∑ i:Axis, X i^2

lemma chart_at (x : Space) : aeval x chart = sq x := by simp [chart,sq,dot,pow_two]
lemma paint_sub (x y : E4) : paint (x-y)=paint x-paint y := by ext1 i; simp [paint]
lemma paint_sq (x : E4) : sq (paint x)=(↑(‖x‖^2):ℂ) := by
  rw [← real_inner_self_eq_norm_sq]; simp only [inner4,sq,dot,paint, Complex.ofReal_sum,Complex.ofReal_mul]
lemma paint_separate {x : E4} (hx : x ≠ 0) : sq (paint x) ≠ 0 := by rw [paint_sq]; exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
lemma dot_self (x : Space) : dot x x=sq x := rfl
lemma dot_comm (x y : Space) : dot x y=dot y x := by unfold dot; congr 1; ext1 i; rw [mul_comm]
lemma dot_add (x y z : Space) : dot (x+y) z=dot x z+dot y z := by simp [dot,add_mul,Finset.sum_add_distrib]
lemma dot_sub (x y z : Space) : dot (x-y) z=dot x z-dot y z := by simp [dot,sub_mul,Finset.sum_sub_distrib]
lemma dot_neg (x y : Space) : dot (-x) y= -dot x y := by simp [dot,Finset.sum_neg_distrib]
lemma dot_scale (x y : Space) (s : ℂ) : dot (s • x) y=s*dot x y := by simp [dot,mul_assoc,Finset.mul_sum]
lemma dot_scale' (x y : Space) (s : ℂ) : dot x (s • y)=s*dot x y := by rw [dot_comm, dot_scale,dot_comm y]
lemma sq_scale (x : Space) (s : ℂ) : sq (s • x)=s^2 * sq x := by unfold sq; rw [dot_scale,dot_scale']; ring
lemma sq_add (x y : Space) : sq (x+y) = sq x+sq y+2*dot x y := by
  rw [sq,dot_add,dot_comm x,dot_comm y,dot_add,dot_add,dot_comm y,dot_self x,dot_self y]; ring
lemma sq_neg (x : Space) : sq (-x)=sq x := by unfold sq; rw [dot_neg,dot_comm x,dot_neg,neg_neg]
lemma sq_sub (x y : Space) : sq (x-y) = sq x+sq y-2*dot x y := by
  rw [sub_eq_add_neg,sq_add,sq_neg,dot_comm x,dot_neg,dot_comm y]; ring
lemma dot_zero (x : Space) : dot x 0=0 := by simp [dot]
lemma sq_zero : sq 0=0 := dot_zero 0
lemma sq_ne : chart≠0 := by
  intro h
  apply paint_separate (x:=basis 0) ?_ (by rw [←chart_at,h,map_zero])
  intro h; have W := congrArg (fun v:E4 ↦ v 0) h; simp at W

def Reads (k : ℕ) (f : E4 → ℂ) (p : Script) := ∀ x : E4, x≠0 →
  aeval (paint x) p = sq (paint x)^(k+1)*f x

def Smooths (p : Script) : Prop := ContDiff ℝ ω (fun x ↦ aeval (paint x) p)
lemma polyReal (p : Script) : Smooths p := by
  induction p using MvPolynomial.induction_on with
  | C c => unfold Smooths; simp only [aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; exact contDiff_const
  | add p q hp hq => unfold Smooths; simp only [map_add]; exact hp.add hq
  | mul_X p i hp => unfold Smooths; simp only [map_mul,aeval_X]; exact hp.mul (Complex.ofRealCLM.contDiff.comp (compAxis i).contDiff)
lemma eqScript {p q : Script} (h : ∀ x, aeval (paint x) p = aeval (paint x) q) : p=q := by
  apply MvPolynomial.funext_set (fun _ ↦ Set.range ((↑) : ℝ → ℂ)) fun _ ↦ infinite_range_of_injective Complex.ofReal_injective
  intro x hx
  choose y hy using fun i ↦ hx i (mem_univ i)
  rw [show x=paint (WithLp.toLp _ y) from funext fun i ↦ (hy i).symm]
  exact h _
lemma eqOpen {p q : Script} {x₀ : E4} (h : ∀ᶠ x in 𝓝 x₀, aeval (paint x) p = aeval (paint x) q) : p=q :=
  eqScript fun i ↦ congr_fun (AnalyticOnNhd.eq_of_eventuallyEq (fun _ _ ↦ (polyReal p).contDiffAt.analyticAt) (𝕜:=ℝ) (fun _ _ ↦ (polyReal q).contDiffAt.analyticAt) h) i
lemma Reads.uniq {k : ℕ} {f : E4 → ℂ} {p q : Script} (h : Reads k f p) (g : Reads k f q) : p=q := by
  have ht : basis 0 ≠ 0 := by intro h; have W := congrArg (fun v:E4 ↦ v 0) h; simp at W
  apply eqOpen (x₀:=basis 0)
  filter_upwards [isOpen_compl_singleton.mem_nhds (show basis 0 ∈ ({0}:Set E4)ᶜ from ht)] with y hy
  exact (h y hy).trans (g y hy).symm

open Tensor

variable {r : ℕ}

def represent (p : T E4 ℂ r) : Script := ∑ a : Fin r → Axis, C (p fun i ↦ basis (a i)) * ∏ i, X (a i)

lemma complex_ray (p : T E4 ℂ r) (x : Space) (s : ℂ) : aeval (s • x) (represent p)=s^r * aeval x (represent p) := by
  unfold represent; simp only [map_sum,map_prod,map_mul,aeval_C,aeval_X,Algebra.algebraMap_self,RingHom.id_apply,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_left_comm ..

lemma evaluates (p : T E4 ℂ r) (x : E4) : aeval (paint x) (represent p)=Tensor.diagonal p x := by
  classical
  have ht : x = ∑ i:Axis, x i • basis i := by symm; ext i; simp
  conv_rhs => rw [ht]
  unfold Tensor.diagonal; unfold represent; simp only [map_sum,map_prod,map_mul,aeval_C,aeval_X,Algebra.algebraMap_self,RingHom.id_apply]
  rw [show p _ = ∑ a:Fin r → Axis, p (fun i ↦ x (a i) • basis (a i)) from ?_]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [p.map_smul_univ]
    simp only [Complex.real_smul,Complex.ofReal_prod]; unfold paint; rw [mul_comm]
  simpa using (p.map_sum_finset (fun (_:Fin r) i ↦ x i • basis i) fun _ ↦ (Finset.univ : Finset Axis))

lemma cleared_ray {f : E4 → ℂ} (H : Maxwell.Free.Pole (r+2) f) : ∃ p : T E4 ℂ r, Reads r f (represent p) := by
  obtain ⟨w,hW,h⟩ := H.precise
  have hw (x) (hx : x ≠ 0) : w x = ((‖x‖^2)^(r+1)) • f x := by simpa [rad] using (h x hx).symm
  have ha (x : E4) (hx : x≠0) (t : ℝ) : w (t • x)=t^r • w x := by
    let f₁ := fun t:ℝ ↦ w (t • x)
    let g₁ := fun t:ℝ ↦ t^r • w x
    refine congr_fun (show f₁=g₁ from AnalyticOnNhd.eq_of_eventuallyEq (𝕜:=ℝ) ?_ ?_ (z₀:=(1:ℝ)) ?_) t
    · unfold f₁; intro t ht; exact (hW.comp (contDiff_id.smul contDiff_const)).contDiffAt.analyticAt
    · intro t ht; exact ((contDiffAt_id.pow r).smul (contDiffAt_const (c:=w x))).analyticAt
    filter_upwards [lt_mem_nhds (by norm_num : (0:ℝ)<1)] with t ht
    unfold f₁ g₁
    rw [hw _ (smul_ne_zero ht.ne' hx), hw _ hx,H.degree t ht x hx,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    simp only [smul_smul]; congr 1
    rw [mul_pow, mul_pow, inv_pow]
    field_simp
    ring
  have he (t : ℝ) : (w ∘ fun x:E4 ↦ t • x)=(fun x:E4 ↦ t^r • w x) := by
    have ht : basis 0 ≠ 0 := by intro h; have W := congrArg (fun v:E4 ↦ v 0) h; simp at W
    refine AnalyticOnNhd.eq_of_eventuallyEq (𝕜:=ℝ) (fun _ _ ↦ (hW.comp ((contDiff_const (c:=t)).smul contDiff_id)).contDiffAt.analyticAt)
      (fun _ _ ↦ ((contDiff_const (c:=t^r)).smul hW).contDiffAt.analyticAt) (z₀:=basis 0) ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds (show basis 0 ∈ ({0}:Set E4)ᶜ from ht)] with y hy
    exact ha y hy t
  refine ⟨Tensor.coeff w r 0, fun x hx ↦ ?_⟩
  rw [evaluates,Planned.AtomRegular.Degree.homog ((hW.of_le le_top).contDiffAt) (fun x t ↦ congr_fun (he t) x),hw x hx,paint_sq]
  simp [Complex.real_smul]

end YM.SchemeConversionRG11.Corona
