import YM.RG01.Kernel.Caliber
import YM.RG01.Analytic.Cauchy
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!
# Conditional generating functions in ambient affine variables

Encode coarse-angle and source simultaneous perturbations as an affine
complex factor in the exponent of the kernel, not differentiating its
input conditional distribution or dividing partition functions. Relative
moments have entire functional expansions, not just diagonal analytic
curves. Op price uses a convenient norm only to prove all derivatives
exist; can use *any* direction costs covering the script, including true
l1 costs uniform in scale and volume, to pay the actual mixed coefficients
or inserts. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Kernel
open Function Filter Set MeasureTheory Complex Metric Topology Finset ENNReal
open scoped Topology ContDiff BigOperators Classical NNReal ENNReal
variable {κ Ω:Type}[Fintype κ][MeasurableSpace Ω]{μ:Measure Ω}
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]

-- use Type0 everywhere for Caliber, maybe generalize later
-- wheel law
structure Wheel (μ:Measure Ω) (Z:κ→Ω→ E→L[ℂ] ℂ) (K:ℝ): Prop where
  sign : 0 ≤ K
  uniform i p : ‖Z i p‖ ≤ K
  measurable (i) (y:E) : AEStronglyMeasurable (fun p=>Z i p y) μ

def generating (w:κ→Ω→ℝ)(Z:κ→Ω→ E→L[ℂ] ℂ)(μ:Measure Ω)(F:κ→Ω→ℂ)(z:E):ℂ:=
  moment w μ (fun i u=>F i u*Complex.exp (Z i u z))

-- licenses and exact series
variable {w:κ→Ω→ℝ}(H : Caliber w μ) {Z:κ→Ω→ E→L[ℂ] ℂ}{K:ℝ}(L:Wheel μ Z K)
variable {F:κ→Ω→ℂ}{b:ℝ}(he:Bounded μ F b)
namespace Wheel

def carrier {m:ℕ} (Z:κ→Ω→ E→L[ℂ] ℂ)(F:κ→Ω→ℂ)(X:Fin m→E)(i:κ)(U:Ω):ℂ := F i U*∏ j,Z i U (X j)

include he L
omit [Fintype κ] in
lemma tilt_charge (x:E)(p:ℝ)(_hp:0≤p)(h:∀ i U,‖Z i U x‖ ≤ p) (hb:0≤b):
    Bounded μ (fun i U=> F i U*Complex.exp (Z i U x)) (b*Real.exp p):= by
  constructor
  · intro i; refine (he.1 i).mul (Complex.continuous_exp.comp_aestronglyMeasurable (L.measurable _ _))
  intro i U; rw [norm_mul,Complex.norm_exp]
  exact mul_le_mul (he.2 i U) (Real.exp_monotone ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (h i U)))) (Real.exp_pos _).le hb
omit [Fintype κ] in
lemma pay {m:ℕ} (Y:Fin m→E)(p:Fin m→ℝ) (hp:∀ i U j, ‖Z i U (Y j)‖≤p j)(_hq:∀ j,0≤p j) (hb:0≤b):
    Bounded μ (carrier Z F Y) (b * ∏ j,p j) := by
  constructor
  · intro i; apply (he.1 i).mul (Finset.aestronglyMeasurable_fun_prod _ (fun _ _=> L.measurable _ _))
  intro i U; rw [carrier,norm_mul,norm_prod]; refine mul_le_mul (he.2 i U) (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun k _=> hp i U k)) (Finset.prod_nonneg (fun _ _=> norm_nonneg _)) hb

omit [Fintype κ] in
lemma pay_norm {m:ℕ}(Y:Fin m→E) (hb:0≤b): Bounded μ (carrier Z F Y) (b*K^m * ∏ j, ‖Y j‖):= by
  have h:=L.pay he Y (fun j=> K*‖Y j‖) (fun i U j=> ((Z i U).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (L.uniform i U) (norm_nonneg _))) (fun j=>mul_nonneg L.sign (norm_nonneg _)) hb
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_fin,mul_assoc] using h

variable (hb:0≤b)
include hb H
variable {m:ℕ}

omit H L he hb [Fintype κ] [MeasurableSpace Ω] in
lemma carrier_insert [DecidableEq (Fin m)] (Y:Fin m→E)(x:E)(i t p):
    carrier Z F (update Y i x) t p = Z t p x*(F t p*∏ j∈(univ.erase i),Z t p (Y j)):= by
  unfold carrier; rw [← mul_prod_erase _ _ (mem_univ i),update_self]
  rw [Finset.prod_congr rfl (fun j hj=>show Z t p (update Y i x j)= Z t p (Y j) from by rw [update_of_ne (mem_erase.mp hj|>.1)])]; ring

def terms (m:ℕ): MultilinearMap ℂ (fun _:Fin m=>E) ℂ where
  toFun X:= moment w μ (carrier Z F X)
  map_update_add' := by
    intro d X i x y
    unfold moment; rw [← sum_add_distrib]; refine sum_congr rfl (fun t _=>?_)
    rw [← integral_add (H.funds (L.pay_norm he (update X i x) hb) t) (H.funds (L.pay_norm he (update X i y) hb) t)]
    apply integral_congr_ae; filter_upwards with p
    rw [carrier_insert,carrier_insert,carrier_insert, map_add]; ring
  map_update_smul' := by
    intro d X i c x
    unfold moment; rw [smul_eq_mul,mul_sum]; refine sum_congr rfl (fun t _=>?_)
    rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with p
    rw [carrier_insert,carrier_insert,map_smul,smul_eq_mul]; ring

def wheelSeries : FormalMultilinearSeries ℂ E ℂ := fun m=> (m.factorial:ℂ)⁻¹ • (L.terms H he hb m).mkContinuous (b*K^m)
    (fun X=> H.price (L.pay_norm he X hb))

lemma series_cap (m:ℕ): ‖L.wheelSeries H he hb m‖ ≤ b * (K^m / m.factorial):=by
  unfold wheelSeries; rw [norm_smul,norm_inv,Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left (MultilinearMap.mkContinuous_norm_le _ (show 0≤ b*K^m from mul_nonneg hb (pow_nonneg L.sign _)) _) (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq ?_
  rw [div_eq_mul_inv]; ring

lemma repack (n:ℕ)(x:Fin n→E): L.wheelSeries H he hb n x=moment w μ (fun i p=>F i p*(∏ j,Z i p (x j))/n.factorial):= by
  change ((n.factorial:ℂ)⁻¹ • moment w μ (carrier Z F x):ℂ)=_
  rw [smul_eq_mul]; unfold moment carrier
  simp_rw [Finset.mul_sum,← integral_const_mul]; refine Finset.sum_congr rfl (fun _ _=>integral_congr_ae (ae_of_all _ fun p=>?_)); simp only [div_eq_mul_inv]; ring
lemma radius : (L.wheelSeries H he hb).radius=⊤:=by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  let M:=(r:ℝ)
  have hr:0≤M:=NNReal.coe_nonneg r
  let f m:= b*((K*M)^m/(m.factorial:ℝ))
  apply ((NormedSpace.expSeries_div_hasSum_exp (K*M)).summable.mul_left b).of_nonneg_of_le (fun i=>mul_nonneg (norm_nonneg _) (pow_nonneg hr _)) (fun i=>?_)
  apply (mul_le_mul_of_nonneg_right (L.series_cap H he hb i) (pow_nonneg hr _)).trans_eq
  rw [mul_pow]; ring


lemma expands : HasFPowerSeriesOnBall (generating w Z μ F) (L.wheelSeries H he hb) 0 ⊤ where
  r_le := (L.radius H he hb).ge
  r_pos:= ENNReal.coe_lt_top
  hasSum {y} _:=by
    let φ (n:ℕ) t p:= F t p*(Z t p y)^n/(n.factorial:ℂ)
    let C:=K*‖y‖; have hc:0 ≤ C:=mul_nonneg L.sign (norm_nonneg _)
    let v (n:ℕ):ℝ:= b*C^n / (n.factorial:ℝ)
    have hg:Summable v:=by have h:=(NormedSpace.expSeries_div_hasSum_exp C).summable.mul_left b; simpa [v,mul_div_assoc] using! h
    have hφ n t p : ‖φ n t p‖≤v n:=by
      unfold φ; rw [norm_div,norm_mul,Complex.norm_natCast,norm_pow]
      have ht:‖Z t p y‖≤C:= ((Z t p).le_opNorm _).trans (mul_le_mul_of_nonneg_right (L.uniform t p) (norm_nonneg y))
      exact div_le_div_of_nonneg_right (mul_le_mul (he.2 t p) (pow_le_pow_left₀ (norm_nonneg _) ht _) (pow_nonneg (norm_nonneg _) _) hb) (Nat.cast_nonneg _)
    have hB n:Bounded μ (φ n) (v n):=⟨fun i=>by unfold φ; simp only [div_eq_mul_inv]; exact ((he.1 i).mul ((L.measurable _ _).pow n)).mul (aestronglyMeasurable_const (b:=(n.factorial:ℂ)⁻¹)), hφ n⟩
    let g n t (p:Ω):=(w t p:ℂ)*φ n t p
    have hf t:HasSum (fun n=>∫ p,g n t p∂μ) (∫ p,(w t p:ℂ)*(F t p*Complex.exp (Z t p y))∂μ):=by
      have hS : Summable fun n=>∫ p,‖g n t p‖∂μ:= by
        have hu:= hg.mul_left (∫ p,w t p∂μ)
        apply hu.of_nonneg_of_le (fun i=>integral_nonneg (fun x=>norm_nonneg _))
        intro i; rw [← integral_mul_const]
        exact integral_mono ((H.funds (hB i) t).norm) ((H.fund t).mul_const _) (fun p=>by
          dsimp only [g]; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (H.pos _ _)]; exact mul_le_mul_of_nonneg_left (hφ i t p) (H.pos _ _))
      convert! hasSum_integral_of_summable_integral_norm (F:=fun n p=>g n t p) (fun n=>H.funds (hB n) t) hS using 1
      apply integral_congr_ae; filter_upwards with p
      unfold g φ; simp_rw [mul_div_assoc,tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq, Complex.exp_eq_exp_ℂ]
    simp only [zero_add]
    have hh:=hasSum_sum (s:= Finset.univ) (fun t _=>hf t)
    convert! hh using 1
    · ext1 n
      rw [L.repack H he hb]
      unfold moment
      simp only [prod_const,card_univ,Fintype.card_fin]; rfl

theorem atZero (n:ℕ)(x:Fin n→E): iteratedFDeriv ℂ n (generating w Z μ F) 0 x = moment w μ (carrier Z F x):=by
  rw [(L.expands H he hb).iteratedFDeriv_eq_sum_of_completeSpace]
  have he (i:Equiv.Perm (Fin n)): L.wheelSeries H he hb n (fun j=>x (i j))=((n.factorial:ℂ)⁻¹ • moment w μ (carrier Z F x):ℂ):= by
    change (n.factorial:ℂ)⁻¹ • moment w μ (carrier Z F (fun j=>x (i j)))= _
    have ha(t:κ)(p:Ω): carrier Z F (fun j=>x (i j)) t p=carrier Z F x t p:= by unfold carrier; rw [show (∏ j, Z t p (x (i j)))=(∏ j,Z t p (x j)) from Equiv.prod_comp i (fun j=> Z t p (x j))] -- extra paren
    unfold moment; simp_rw [ha]
  simp_rw [he]; rw [Finset.sum_const,card_univ, Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul,smul_eq_mul,←mul_assoc,mul_inv_cancel₀,one_mul]
  exact_mod_cast Nat.factorial_ne_zero n

-- full analyticity at any displacement. hU grows, not claiming uniform in volume here. uniformly bounded on scaled subdiscs by Caliber.
theorem entire : AnalyticOnNhd ℂ (generating w Z μ F) Set.univ := by
  intro z hz
  let f i x:=F i x * Complex.exp (Z i x z)
  have h:Bounded μ f (b*Real.exp (K*‖z‖)):=L.tilt_charge he z (K*‖z‖) (mul_nonneg L.sign (norm_nonneg _)) (fun i x=>
    ((Z i x).le_opNorm z).trans (mul_le_mul_of_nonneg_right (L.uniform i x) (norm_nonneg _))) hb
  have hg:= (L.expands H h (mul_nonneg hb (Real.exp_pos _).le)).analyticAt
  have hf : generating w Z μ F=(generating w Z μ f) ∘ (fun x=>x-z):=by
    ext1 x; unfold generating comp f; apply congr_arg (moment w μ); funext i p; dsimp only; rw [map_sub,Complex.exp_sub]; field_simp [Complex.exp_ne_zero]
  rw [hf]; apply AnalyticAt.comp (f:=fun x=>x-z) (g:=generating w Z μ f)
  · simpa using! hg
  exact (analyticAt_id (𝕜:=ℂ)).sub analyticAt_const
end Wheel
end YM.RG01.Kernel
