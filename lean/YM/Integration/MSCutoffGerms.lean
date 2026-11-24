import YM.FVA2.Pond
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Analysis.Polynomial.Basic

/-! Subexponential cutoff germs for the original logarithmic regulator.
An engineering-lowering exponential times a scale polynomial can belong
to this ring only when the polynomial itself is zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSCutoffGerms

open Filter Set
open scoped Topology BigOperators Classical

variable {I J : Type*} (l : Filter I) (t : I → ℝ)

def weight (e : ℝ) (i : I) : ℂ := Real.exp (-e * t i)

def Moderate (f : I → ℂ) : Prop :=
  ∀ e : ℝ, 0 < e → Tendsto (fun i => weight t e i * f i) l (𝓝 0)

variable {l t}

theorem vanishes (ht : Tendsto t l atTop) (e : ℝ) (he : 0 < e) :
    Tendsto (weight t e) l (𝓝 0) := by
  change Tendsto (fun x => ((Real.exp (-e*t x) : ℝ) : ℂ)) l (𝓝 0)
  simpa only [Function.comp_def, Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto 0).comp
      (Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (neg_lt_zero.mpr he)))

theorem convergent {f : I → ℂ} {c : ℂ} (ht : Tendsto t l atTop)
    (hf : Tendsto f l (𝓝 c)) : Moderate l t f := fun e he => by
  simpa only [zero_mul] using (vanishes ht e he).mul hf

theorem plus {f g : I → ℂ} (hf : Moderate l t f) (hg : Moderate l t g) :
    Moderate l t (f+g) := fun e he => by
  simpa only [Pi.add_apply, mul_add, zero_add] using (hf e he).add (hg e he)

theorem minus {f : I → ℂ} (hf : Moderate l t f) : Moderate l t (-f) := fun e he => by
  simpa only [Pi.neg_apply, mul_neg, neg_zero] using (hf e he).neg

theorem times {f g : I → ℂ} (hf : Moderate l t f) (hg : Moderate l t g) :
    Moderate l t (f*g) := by
  intro e he
  have h : 0 < e/2 := by positivity
  have eqw (i : I) : weight t e i = weight t (e/2) i * weight t (e/2) i := by
    unfold weight
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  convert (hf (e/2) h).mul (hg (e/2) h) using 1
  · funext i
    rw [eqw, Pi.mul_apply]
    ring
  · simp

theorem equal {f g : I → ℂ} (h : f =ᶠ[l] g) (hf : Moderate l t f) : Moderate l t g :=
  fun e he => (hf e he).congr' (h.mono fun i hi => congrArg (weight t e i * ·) hi)

def hom (l : Filter I) : (I → ℂ) →+* Germ l ℂ where
  toFun f := (f : Germ l ℂ)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def functions (ht : Tendsto t l atTop) : Subring (I → ℂ) where
  carrier := Moderate l t
  zero_mem' := convergent ht (tendsto_const_nhds (x := (0:ℂ)))
  one_mem' := convergent ht (tendsto_const_nhds (x := (1:ℂ)))
  add_mem' := plus
  neg_mem' := minus
  mul_mem' := times

def ring (ht : Tendsto t l atTop) : Subring (Germ l ℂ) := (functions ht).map (hom l)

theorem member (ht : Tendsto t l atTop) (f : I → ℂ) :
    (f : Germ l ℂ) ∈ ring ht ↔ Moderate l t f := by
  constructor
  · rintro ⟨g, hg, he⟩
    exact equal (Germ.coe_eq.mp he) hg
  · intro hf
    exact ⟨f, hf, rfl⟩

theorem reciprocal (ht : Tendsto t l atTop) {f : I → ℂ} {c : ℂ}
    (hf : Tendsto f l (𝓝 c)) (hc : c ≠ 0) :
    IsUnit (⟨(f : Germ l ℂ), (member ht f).mpr (convergent ht hf)⟩ : ring ht) := by
  let b : ring ht := ⟨(fun i => (f i)⁻¹ : I → ℂ), (member ht _).mpr
    (convergent ht (hf.inv₀ hc))⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨b, Subtype.ext ?_⟩
  apply Germ.coe_eq.mpr
  exact (hf.eventually_ne hc).mono fun i hi => mul_inv_cancel₀ hi

theorem log_clock (ht : Tendsto t l atTop) : Moderate l t (fun i => (t i : ℂ)) := by
  intro e he
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (ht.const_mul_atTop he)
  have h' : Tendsto (fun i => (e*t i) * Real.exp (-(e*t i))) l (𝓝 0) := by
    simpa only [Function.comp_def, pow_one] using h
  have h'' := (tendsto_const_nhds (x := e⁻¹)).mul h'
  have heq (i : I) : Real.exp (-e*t i) * t i =
      e⁻¹ * ((e*t i) * Real.exp (-(e*t i))) := by
    rw [neg_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ he.ne', one_mul, mul_comm]
  simpa only [weight, Function.comp_def, ← Complex.ofReal_mul, heq, Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto 0).comp
      (show Tendsto (fun i => e⁻¹*((e*t i)*Real.exp (-(e*t i)))) l (𝓝 0) by
        simpa only [mul_zero] using h'')

theorem polynomial (ht : Tendsto t l atTop) (μ : ℝ) (p : Polynomial ℝ) :
    Moderate l t (fun i => ((p.eval (μ-t i) : ℝ) : ℂ)) := by
  let S := functions ht
  have x : (fun i => ((μ-t i : ℝ) : ℂ)) ∈ S := by
    have m : (fun _ : I => (μ : ℂ)) ∈ S := convergent ht tendsto_const_nhds
    have hs : (fun i => (μ : ℂ)-(t i : ℂ)) ∈ S := S.sub_mem m (log_clock ht)
    simpa only [Complex.ofReal_sub] using hs
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hs : Moderate l t (fun i => ((p.eval (μ-t i) : ℝ) : ℂ)+((q.eval (μ-t i) : ℝ) : ℂ)) :=
      plus hp hq
    simpa only [Polynomial.eval_add, Complex.ofReal_add] using hs
  | monomial n c =>
    have hc : (fun _ : I => (c : ℂ)) ∈ S := convergent ht tendsto_const_nhds
    have hs : Moderate l t (fun i => (c : ℂ)*(((μ-t i : ℝ) : ℂ)^n)) :=
      S.mul_mem hc (S.pow_mem x n)
    simpa only [Polynomial.eval_monomial, Complex.ofReal_mul, Complex.ofReal_pow] using hs

theorem shifted (ht : Tendsto t l atTop) (μ : ℝ) : Tendsto (fun i => μ - t i) l atBot := by
  rw [tendsto_atBot]
  intro x
  filter_upwards [(tendsto_atTop.mp ht) (μ-x)] with i hi
  linarith

theorem poly_constant [NeBot l] {s : I → ℝ} (hs : Tendsto s l atBot)
    (p : Polynomial ℝ) {c : ℝ} (hp : Tendsto (fun i => p.eval (s i)) l (𝓝 c)) :
    p = Polynomial.C c := by
  have hd : p.degree ≤ 0 := by
    by_contra! h
    exact not_tendsto_atTop_of_tendsto_nhds (continuous_abs.continuousAt.tendsto.comp hp)
      ((p.abs_tendsto_atBot h).comp hs)
  have h0 := Polynomial.eq_C_of_degree_le_zero hd
  have h' : p.coeff 0 = c := by
    apply tendsto_nhds_unique (f := fun i => p.eval (s i)) _ hp
    have he i : p.eval (s i)=p.coeff 0 :=
      (congrArg (Polynomial.eval (s i)) h0).trans Polynomial.eval_C
    simp_rw [he]
    exact tendsto_const_nhds
  exact h0.trans (congrArg Polynomial.C h')

theorem no_lower [NeBot l] (ht : Tendsto t l atTop) (μ d : ℝ) (hd : 0 < d)
    (p : Polynomial ℝ)
    (h : Moderate l t (fun i => (Real.exp (d*t i) * p.eval (μ-t i) : ℝ))) :
    p = 0 := by
  have he (i : I) :
      weight t d i * ((Real.exp (d*t i)*p.eval (μ-t i) : ℝ) : ℂ) =
        ((p.eval (μ-t i) : ℝ) : ℂ) := by
    unfold weight
    rw [← Complex.ofReal_mul, ← mul_assoc, ← Real.exp_add]
    simp
  have hp : Tendsto (fun i => ((p.eval (μ-t i) : ℝ) : ℂ)) l (𝓝 0) := by
    simpa only [he] using h d hd
  have hr : Tendsto (fun i => p.eval (μ-t i)) l (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_re,Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hp
  simpa using poly_constant (shifted ht μ) p hr

/-- Finite true continuum rows may be complex even though each register
polynomial is real. Constancy follows for the actual complex contraction. -/
theorem contract [Fintype J] [NeBot l] {s : I → ℝ} (hs : Tendsto s l atBot)
    (p : J → Polynomial ℝ) (z : J → ℂ) (w : ℂ)
    (hw : Tendsto (fun i => ∑ j, (((p j).eval (s i) : ℝ) : ℂ)*z j) l (𝓝 w)) :
    ∑ j, (((p j).eval 0 : ℝ) : ℂ)*z j = w := by
  classical
  let u := ∑ j, p j * Polynomial.C (z j).re
  let v := ∑ j, p j * Polynomial.C (z j).im
  have ur (x : ℝ) : (∑ j, (((p j).eval x : ℝ) : ℂ)*z j).re = u.eval x := by
    simp [u, Complex.re_sum, Polynomial.eval_finsetSum, Complex.mul_re]
  have vi (x : ℝ) : (∑ j, (((p j).eval x : ℝ) : ℂ)*z j).im = v.eval x := by
    simp [v, Complex.im_sum, Polynomial.eval_finsetSum, Complex.mul_im]
  have hu := poly_constant hs u
    (show Tendsto (fun i => u.eval (s i)) l (𝓝 w.re) by
      simpa only [Function.comp_def, ur] using Complex.continuous_re.continuousAt.tendsto.comp hw)
  have hv := poly_constant hs v
    (show Tendsto (fun i => v.eval (s i)) l (𝓝 w.im) by
      simpa only [Function.comp_def, vi] using Complex.continuous_im.continuousAt.tendsto.comp hw)
  apply Complex.ext
  · exact (ur 0).trans (by rw [hu,Polynomial.eval_C])
  · exact (vi 0).trans (by rw [hv,Polynomial.eval_C])

end YM.Integration.MSCutoffGerms
