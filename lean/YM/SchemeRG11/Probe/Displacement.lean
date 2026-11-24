import YM.SchemeRG11.Probe.ZeroCone
import YM.Next.MAXWELL.Steps
/-!
Complex rational detector polynomials for FREE shell readings of the
pinned Maxwell comparator. Computes derivatives in the actual real
coordinate convention; no Fourier transformation/covariance assumptions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.ConeProbe
open MvPolynomial Finset YM.Maxwell Filter Set Analysis YM.Maxwell.Free
open scoped BigOperators ContDiff Topology Classical

def cast4 (x : E4) : Vec := fun i => (x i : ℂ)

def scored (p : Pol) (x : E4) := eval (cast4 x) p

lemma scored_quad (x : E4) : scored quad x = ((‖x‖^2:ℝ):ℂ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [scored,quad,map_sum,map_mul,eval_X,Complex.ofReal_sum,cast4,pow_two,
    Complex.ofReal_mul]

lemma quad_not_zero : quad ≠ 0 := by
  intro h
  have hh := scored_quad (basis 0)
  rw [h] at hh
  norm_num [scored] at hh

lemma scored_add (p q : Pol) : scored (p+q) = scored p + scored q := funext (fun _ => map_add ..)
lemma scored_sub (p q : Pol) : scored (p-q) = scored p - scored q := funext (fun _ => map_sub ..)
lemma scored_mul (p q : Pol) : scored (p*q) = scored p * scored q := funext (fun _ => map_mul ..)
lemma scored_C (u : ℂ) : scored (C u) = fun _ => u := funext fun _ => eval_C u
lemma scored_X (i : Axis) : scored (X i) = fun x => cast4 x i := funext fun _ => eval_X i
lemma scored_zero : scored 0 = 0 := funext fun _ => map_zero ..
lemma scored_one : scored 1 = 1 := funext fun _ => map_one ..
lemma scored_nat (n : ℕ) (x : E4) : scored (↑n) x = n := map_natCast ..

lemma colorAxis (i : Axis) : scored (X i) = Complex.ofRealCLM ∘ compAxis i := scored_X i
lemma scored_diff (p : Pol) : Differentiable ℝ (scored p) := by
  induction p using MvPolynomial.induction_on with
  | C u => rw [scored_C]; exact differentiable_const _
  | add p q hp hq => rw [scored_add]; exact hp.add hq
  | mul_X p i hp => rw [scored_mul,colorAxis]; exact hp.mul (Complex.ofRealCLM.differentiable.comp (compAxis i).differentiable)

lemma grad_score (p : Pol) (i : Axis) (x : E4) : grad i (scored p) x = scored (pderiv i p) x := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [scored_C,pderiv_C, scored_zero]; simp [grad,D]
  | add p q hp hq =>
    rw [scored_add,map_add,scored_add,grad,D,fderiv_add (scored_diff _ _) (scored_diff _ _)]
    change grad i (scored p) x + grad i (scored q) x = _
    rw [hp,hq,Pi.add_apply]
  | mul_X p j hp =>
    have he : grad i (scored (X j)) x = scored (pderiv i (X j)) x := by
      rw [colorAxis,grad,D,fderiv_comp x Complex.ofRealCLM.differentiableAt (compAxis j).differentiableAt,
        Complex.ofRealCLM.fderiv,(compAxis j).fderiv]
      change ((basis i j:ℝ):ℂ)=_
      rcases eq_or_ne i j with h|h
      · subst j
        rw [pderiv_X_self,basis_eq,if_pos rfl]
        simp only [Complex.ofReal_one,scored_one]
        rfl
      rw [pderiv_X_of_ne (Ne.symm h),basis_eq,if_neg (Ne.symm h)]
      simp only [Complex.ofReal_zero,scored_zero]
      rfl
    rw [pderiv_mul,scored_add,scored_mul,scored_mul,scored_mul]
    rw [Pi.add_apply,Pi.mul_apply,Pi.mul_apply,←hp,←he,grad,D,
      fderiv_mul (scored_diff _ _) (scored_diff _ _)]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
    unfold D
    ring

/-- The real tested rationals determine the polynomial exactly. -/
lemma scored_inj (p r : Pol) (h : ∀ x : E4, x≠0 → scored p x=scored r x) : p=r := by
  have hh : p*quad=r*quad := by
    apply MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ)) fun _ =>
        Set.infinite_range_of_injective Complex.ofReal_injective
    intro x hx
    choose w hw using fun i => hx i (Set.mem_univ _)
    let z : E4 := WithLp.toLp 2 w
    have hv : cast4 z=x:=funext hw
    rw [←hv]
    change scored (p*quad) z=scored (r*quad) z
    rw [scored_mul,scored_mul, Pi.mul_apply,Pi.mul_apply]; by_cases H : z=0
    · rw [scored_quad,H,norm_zero]; simp
    rw [h _ H]
  exact mul_right_cancel₀ quad_not_zero hh

-- `Holds P F n`: denominator q^(n+1).
def Holds (P : Pol) (f : E4→ℝ) (n : ℕ) :=
    ∀ x : E4,x≠0 → scored P x = (scored quad x)^(n+1)*(f x : ℂ)

lemma Holds.unique {p r : Pol} {n : ℕ} {f : E4→ℝ} (h : Holds p f n) (e : Holds r f n) : p=r :=
    scored_inj _ _ fun x hx => (h x hx).trans (e x hx).symm
lemma Holds.const {p : Pol} {n : ℕ} {f : E4→ℝ} (h : Holds p f n) (c : ℝ) :
    Holds (C (c:ℂ)*p) (fun x=> c*f x) n := by
  intro x hx
  rw [scored_mul, Pi.mul_apply,h _ hx,scored_C]; push_cast; ring
lemma Holds.add {p q : Pol} {n : ℕ} {f g : E4 → ℝ} (h : Holds p f n) (e : Holds q g n) :
    Holds (p+q) (f+g) n := by
  intro x hx
  rw [scored_add,Pi.add_apply,h _ hx,e _ hx]; simp only [Pi.add_apply]; push_cast; ring
lemma Holds.sub {p q : Pol} {n : ℕ} {f g : E4 → ℝ} (h : Holds p f n) (e : Holds q g n) :
    Holds (p-q) (f-g) n := by
  intro x hx
  rw [scored_sub,Pi.sub_apply,h _ hx,e _ hx]; simp only [Pi.sub_apply]; push_cast; ring

lemma reflect_real (f : E4 → ℝ) (x : E4) (hx : DifferentiableAt ℝ f x) (i : Axis) :
    grad i (fun y => (f y:ℂ)) x = ((grad i f x:ℝ):ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x _ = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt hx,Complex.ofRealCLM.fderiv]; rfl

lemma Holds.raise {p : Pol} {n : ℕ} {f : E4 → ℝ} (h : Holds p f n)
    (hf : ∀ x : E4,x ≠ 0 → DifferentiableAt ℝ f x) (i : Axis) :
    Holds (raiseAt i n p) (grad i f) (n+1) := by
  intro x hx
  let z := scored quad
  let w : E4→ℂ := fun x => (f x:ℂ)
  have hh : grad i (scored p) x = grad i ((z^(n+1))*w) x := by
    apply GermD (basis i)
    filter_upwards [open_away.mem_nhds (show x∈away from hx)] with y hy
    simpa only [Pi.pow_apply,Pi.mul_apply] using h y hy
  have hu : DifferentiableAt ℝ w x := Complex.ofRealCLM.differentiableAt.comp _ (hf x hx)
  have hv : DifferentiableAt ℝ z x := scored_diff _ _
  have hQ : scored quad x = z x := rfl
  have he : grad i (z^(n+1)) x = ((n:ℂ)+1)*z x^n*grad i z x := by
    unfold grad D
    have H := hv.hasFDerivAt.pow (n+1)
    rw [show z^(n+1)=(fun x=> z x^(n+1)) by ext1 x; rw [Pi.pow_apply], H.fderiv]
    simp
  have ht : grad i ((z^(n+1))*w) x =
      grad i (z^(n+1)) x * w x + z x^(n+1) * grad i w x := by
    unfold grad D
    rw [fderiv_mul (by fun_prop) hu]
    simp [mul_comm,add_comm]
  rw [ht,he,grad_score, show grad i z x = scored (pderiv i quad) x from grad_score ..,
    partial_sq, show grad i w x=((grad i f x:ℝ):ℂ) from reflect_real f x (hf x hx) i] at hh
  rw [raiseAt,scored_sub,scored_mul,scored_mul,scored_mul]
  simp only [Pi.sub_apply,Pi.mul_apply, h _ hx,hQ,hh,scored_C]
  unfold w at *
  rw [scored_mul, Pi.mul_apply,show scored 2 x=(2:ℂ) from map_ofNat ..]
  ring

lemma green_top : Holds (C (normal :ℂ)) Green 0 := by
  intro x hx
  have hh : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [scored_quad, Green, scored_C]
  norm_cast
  field_simp
  congr 1; field_simp
  ring

end YM.SchemeRG11.ConeProbe
