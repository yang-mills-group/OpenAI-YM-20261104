import YM.RG02.Limit.Plane

/-!
Parameter-ray Laplace tests without shifting the scheme or its covariance.
Kernel preserves actual parameter-direction (1,x) before Wick; stationary
mean applied to ACCOUNT for all interactions. The auxiliary scalar λ*cₜ²
for domination will cancel exactly. Boundary insertions don't need an
analytic function of t at t=0 except their scaled analytic packets; any
Laurent prefactors must be budgeted separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Therm
open Filter Function MeasureTheory Set Metric
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Asym Wick
open GaussianScore PowerSeries
open scoped ContDiff Topology Classical Real BigOperators
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]

def Steer (Γ : Law E) (f : ℝ × E→ℝ)(r : ℝ)(b : E) : Prop := Stationary f ∧
    ∀ (a : ℝ)(x:E), jet f 2 (a,x)=a^2*r+Γ.P (x - a • b) (x - a • b)/2

namespace Steer
variable {Γ : Law E} {f : ℝ× E→ℝ}{r : ℝ}{b : E} (H : Steer Γ f r b)
include H

def raised (f : ℝ× E→ℝ) (s : ℝ) (v : ℝ×E) := f v + s*v.1^2

omit [FiniteDimensional ℝ E] in
lemma raised_smooth (s : ℝ) : ContDiffAt ℝ ∞ (raised f s) 0 := H.1.smooth.add (contDiffAt_const.mul (contDiffAt_fst.pow ..))
lemma scored (s a : ℝ)(x : E)(i : ℕ) : jet (raised f s) i (a,x)=jet f i (a,x) + if i=2 then s*a^2 else 0 := by
   have he : layer (raised f s) (a,x) = layer f (a,x) + PowerSeries.monomial 2 (Complex.ofReal (s*a^2)) := by
      apply Near.unique' (layer_ray (H.raised_smooth s) (a,x))
      convert! Near.incline (layer_ray H.1.smooth (a,x)) (Near.mono (Complex.ofReal (s*a^2)) 2) using 1
      funext t; simp only [raised,Prod.smul_mk,Complex.real_smul,Pi.add_apply,Complex.ofReal_add,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_pow]; ring
   have hh := congr_arg (fun p : PowerSeries ℂ => coeff i p) he
   simp only [layer,coeff_mk,map_add,coeff_monomial] at hh
   apply Complex.ofReal_injective; rw [hh]; split <;> simp

lemma still (s : ℝ) : Steer Γ (raised f s) (r+s) b := by
   refine ⟨⟨H.raised_smooth s,by rw [raised,H.1.base0]; simp,?_⟩,fun i x =>?_⟩
   · intro ⟨x,y⟩; rw [H.scored,H.1.base1]; simp
   rw [H.scored,H.2,if_pos rfl]; ring

lemma slopes (m : ℝ)(x : ℝ×E) : Asym.driven (raised f m) x = Asym.driven f x := by
   rcases x with ⟨a,u⟩
   ext k
   · simp_rw [Asym.driven, PowerSeries.coeff_mk,Radial.layers,H.scored]; by_cases h:k=0 <;> simp [h]

lemma boost (hr : r>0) : ∃ c>0,∀ x : ℝ× E,c*‖x‖^2≤jet f 2 x := by
   obtain ⟨c,hc,h⟩ := Γ.slope
   apply quadratic_min; intro ⟨i,x⟩ hi
   rw [H.2]; by_cases he : i=0
   · subst i; have hx : x≠0 := fun hh => hi (by rw [hh]; rfl)
     simp only [zero_pow (by omega : 2 ≠ 0),zero_smul,sub_zero,zero_mul,zero_add]
     exact lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hx))) (h x)
   exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero he) hr) (le_trans (by positivity) (h _))
end Steer

def leading (Γ : Law E) [MeasurableSpace E] (μ : Measure E)(r : ℝ) := mass Γ μ * Real.exp (-r)

section polys
variable {X : Type}
def bend (a x : E) := ((1:ℝ),x+a)
omit [FiniteDimensional ℝ E] in
lemma bent (a : E) : bend a= fun x => LinearMap.inr ℝ ℝ E x + ((1:ℝ),a) := funext fun _ => Prod.ext (zero_add (1:ℝ)).symm rfl

lemma displays (f : ℝ × E→ℝ)(a : E)(i : ℕ) : Wires fun x => (coeff i (Asym.driven f (bend a x))) := by
   simp_rw [Asym.driven,PowerSeries.coeff_mk,Radial.layers]
   by_cases h : i=0
   · simp [h]; exact Wires.const 0
   simp only [h,if_false,add_zero,Complex.ofReal_neg]; rw [bent]; exact (Wires.lists _ _ _ _).neg

omit [FiniteDimensional ℝ E] in
private lemma scheme_product (f g:E→PowerSeries ℂ)(i : ℕ)(h : ∀ k,Wires fun x=>coeff k (f x))(hg : ∀ k,Wires fun x=>coeff k (g x)) :
   Wires (fun x=> coeff i (f x*g x)) := by
   simp_rw [coeff_mul]; exact Wires.sum_x (Finset.antidiagonal i) (fun p x => coeff p.1 (f x)*coeff p.2 (g x)) fun p _=>(h p.1).mul (hg p.2)

lemma row_wires (K:ℝ× E→ℂ)(a : E)(n : ℕ) : Wires fun x => coeff n (Asym.ribbon K (bend a x)) := by
   simp_rw [Asym.ribbon_coeff]; rw [bent]
   exact Wires.add (Wires.lists _ _ _ _) ((Wires.lists _ _ _ _).smul Complex.I)

def pulsed (f : ℝ × E→ℝ)(K:ℝ× E→ℂ)(n : ℕ)(b : E)(x : E) :=
    coeff n (ribbon K (bend b x) * Asym.ex (Asym.driven f (bend b x)))
set_option maxHeartbeats 400000 in
lemma edgewired (f : ℝ × E→ℝ)(K:ℝ× E→ℂ)(b : E)(n : ℕ) : Wires (pulsed f K n b) := by
   let g:=fun x:E => driven f (bend b x)
   apply scheme_product (fun x=>ribbon K (bend b x)) (fun x=>Asym.ex (g x)) n (row_wires K b)
   intro k; simp_rw [Asym.ex,PowerSeries.coeff_mk]
   have he (j i:ℕ) : Wires (fun x => coeff i ((g x)^j)) := by
      induction j generalizing i with
      | zero => simp_rw [pow_zero]; exact Wires.const _
      | succ d ih => simp_rw [pow_succ]; exact scheme_product (fun x=>g x^d) g i ih (displays f b)
   exact Wires.sum_x _ (fun i x=>(i.factorial:ℂ)⁻¹ * coeff k (g x^i)) fun i _ => (he i k).smul _

def shuttle (Γ : Law E)(f : ℝ × E→ℝ)(K:ℝ× E→ℂ)(b:E) := PowerSeries.mk fun n => Wick.weigh Γ (pulsed f K n b)
end polys

variable {Γ : Law E} {f : ℝ× E→ℝ}{r : ℝ}{b : E} (H : Steer Γ f r b)
variable [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant][NeZero μ]

omit [μ.IsAddRightInvariant] in
lemma leading_pos (Γ : Law E) (r : ℝ) : 0 < leading Γ μ r := by unfold leading; exact mul_pos (mass_pos Γ μ) (Real.exp_pos _)

include H

lemma integral_charge (K:ℝ× E→ℂ)(n : ℕ) : ∫ u:E, visibly f K n (1,u) ∂μ = ↑(leading Γ μ r) * coeff n (shuttle Γ f K b) := by
   rw [shuttle,coeff_mk,agrees Γ μ (edgewired ..)]
   let g (x:E) := visibly f K n (1,x)
   have he (x:E) : g (x+b)= ↑(Real.exp (-r))* (pulsed f K n b x * ↑(Γ.kern x)) := by
      unfold g visibly; rw [show Radial.kernel f ((1:ℝ),x+b)=Real.exp (-r)*Γ.kern x from ?_]
      · rw [Complex.ofReal_mul]; unfold pulsed bend; ring
      rw [GaussianScore.Law.kern,Radial.kernel,H.2]; rw [← Real.exp_add]; congr 1; simp; ring
   change (∫ x,g x ∂μ) = ↑(leading _ _ _) * Wick.normed _ _ _
   rw [← integral_add_right_eq_self g b]
   simp_rw [he,integral_const_mul]
   unfold leading Wick.normed; rw [Complex.ofReal_mul]
   have h : (↑(mass Γ μ):ℂ) ≠ 0:= Complex.ofReal_ne_zero.mpr (mass_pos Γ μ).ne'
   field_simp

-- Anchors: real Gaussian, actual Haar chart weight belongs inside f,K. g=not a coupling-offset germ.
lemma transmission (hf : Measurable f){K:ℝ× E→ℂ}(hk : ContDiffAt ℝ ∞ K 0)(hm : Measurable K) :
    ∃ u>0,∀ S : ℝ→Set E, Collars u S →
      (∀ᶠ t in Tested.germ, IntegrableOn (sheet f K t) (S t) μ) ∧
      Near (fun t=>(∫ x in S t,sheet f K t x ∂μ)) (C (Complex.ofReal (leading Γ μ r))* shuttle Γ f K b) := by
   let m:=1-r
   have hp : 0<r+m := by unfold m; linarith
   let g:= Steer.raised f m
   have h := H.still m
   obtain ⟨u,hu,HL⟩ := fly μ h.1 (h.boost hp) (hf.add ((measurable_fst.pow_const 2).const_mul m)) hk hm
   let v:ℂ:= ↑(Real.exp m)
   refine ⟨u,hu,fun S hS=>?_⟩
   obtain ⟨hh,hX,hY⟩ := HL S hS
   have he (t:ℝ)(ht : 0<t) (x:E) : sheet f K t x= v * sheet g K t x := by
      unfold sheet; rw [mul_left_comm]; congr 1
      unfold v; rw [← Complex.ofReal_mul, turbine,turbine,← Real.exp_add]; congr 2
      unfold g Steer.raised; dsimp only; have hn:=ht.ne'; field_simp; ring
   constructor
   · filter_upwards [Tested.eventually_pos,hX] with t ht hT
     rw [show sheet f K t = _ from funext (he t ht)]; exact hT.const_mul _
   have hF := Near.scaled hY v
   have h' : C v* (PowerSeries.mk fun n=>∫ x:E, visibly g K n (1,x) ∂μ)=
        C (Complex.ofReal (leading Γ μ r)) * shuttle Γ f K b := by
      ext1 i
      have hW : shuttle Γ g K b=shuttle Γ f K b := by
         ext1 i; simp only [shuttle, coeff_mk]
         congr 1; funext x; unfold pulsed; rw [H.slopes]
      rw [coeff_C_mul,coeff_mk, integral_charge (b:=b) h,coeff_C_mul,hW,← mul_assoc]; congr 1
      unfold v leading; rw [← Complex.ofReal_mul]; congr 1
      rw [mul_left_comm, ← Real.exp_add]; ring_nf
   rw [h'] at hF
   apply Near.same hF
   filter_upwards [Tested.eventually_pos] with t ht
   simp_rw [he t ht,integral_const_mul]; rfl
end YM.RG02.Therm
