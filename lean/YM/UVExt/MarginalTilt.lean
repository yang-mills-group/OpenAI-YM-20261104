import YM.UVExt.TagPrimitive
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Only the selected Gaussian coordinates. No normalization per unused link in the bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay.Gaussian
open RG Lattice Wilson Pressure Stores ConnectedActivityE6 Coat Raw Mask Pulse Itinerary Poll Pond Matrix MeasureTheory Measure
open scoped Topology BigOperators Classical ENNReal

variable {I:Type} [Fintype I] [DecidableEq I]

def value (A:Matrix I I ℝ) (z:Body I) : ℝ := dotProduct z.ofLp (A⁻¹*ᵥ z.ofLp)/2
lemma value_smul (A:Matrix I I ℝ) (r:ℝ) (z:Body I) : value A (r • z) = r^2*value A z := by
 rw [value, WithLp.ofLp_smul,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]
 simp only [smul_eq_mul]; unfold value; ring
lemma value_cont (A:Matrix I I ℝ) : Continuous (value A) := by
 unfold value Matrix.mulVec dotProduct; fun_prop

def pdf (A:Matrix I I ℝ) (z:Body I) := ((Real.sqrt (2*Real.pi))^Fintype.card I)⁻¹ * Real.exp (-Real.log A.det/2-value A z)
lemma cosh (A:Matrix I I ℝ) (hA:A.PosDef) : Poll.sweep A = volume.withDensity (fun z=>ENNReal.ofReal (pdf A z)) := Poll.sweep_pdf hA
lemma prices (A:Matrix I I ℝ) (z) : 0 ≤ pdf A z := by unfold pdf; positivity
lemma measurable_pdf (A:Matrix I I ℝ) : Measurable (pdf A) := by
 refine (continuous_const.mul ?_).measurable
 exact Real.continuous_exp.comp (continuous_const.sub (value_cont A))

def tilt (A:Matrix I I ℝ) (r:ℝ) (z:Body I) := (Real.sqrt r)^Fintype.card I * Real.exp ((1-r)*value A z)
lemma tilt_nn (A:Matrix I I ℝ) (r:ℝ) (z:Body I) : 0≤tilt A r z := mul_nonneg (pow_nonneg (Real.sqrt_nonneg r) _) (Real.exp_pos _).le
lemma tilt_exact (A:Matrix I I ℝ) (r:ℝ) (hr:0≤r) (z:Body I) : tilt A r z * pdf A z = (Real.sqrt r)^Fintype.card I * pdf A (Real.sqrt r • z) := by
 rw [tilt,pdf,pdf,value_smul,Real.sq_sqrt hr]
 rw [show -Real.log A.det/2-r*value A z=(1-r)*value A z+(-Real.log A.det/2-value A z) by ring]
 -- target RHS changed? nth_rw likely wrong index
 rw [Real.exp_add]; ring

lemma pay_real (A:Matrix I I ℝ) (hA:A.PosDef) (g:Body I→ℂ) :
    (∫ z,g z ∂Poll.sweep A) = ∫ z,(pdf A z:ℂ) * g z ∂(volume:Measure (Body I)) := by
  rw [cosh _ hA,integral_withDensity_eq_integral_toReal_smul (measurable_pdf _).ennreal_ofReal (Filter.Eventually.of_forall (fun _=> ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (prices ..),Complex.real_smul]

lemma integral_tilt (A:Matrix I I ℝ) (hA:A.PosDef) (r:ℝ) (hr:0<r) (g:Body I→ℂ) :
    (∫ z,(tilt A r z:ℂ)*g (Real.sqrt r • z) ∂Poll.sweep A) = ∫ z,g z ∂Poll.sweep A := by
 rw [pay_real _ hA,pay_real _ hA]
 let W := fun z=>(pdf A z:ℂ)*g z
 let e := Fintype.card I; let k : ℝ:= √r^e; have hk : 0<k:= pow_pos (Real.sqrt_pos.mpr hr) _
 have h := Measure.integral_comp_smul_of_nonneg (volume:Measure (Body I)) W (Real.sqrt r) (hR:=by positivity)
 rw [show Module.finrank ℝ (Body I)= Fintype.card I from finrank_euclideanSpace] at h
 have hh (z) : (pdf A z:ℂ)*((tilt A r z:ℂ)*g (Real.sqrt r • z)) = k*W (Real.sqrt r • z) := by
    dsimp only [W]; rw [mul_left_comm,←mul_assoc, ←Complex.ofReal_mul, tilt_exact _ _ hr.le,Complex.ofReal_mul,mul_assoc]
    -- attempt
 simp_rw [hh]; rw [MeasureTheory.integral_const_mul]; erw [h]; rw [show (√r ^ Fintype.card I)⁻¹ = k⁻¹ from rfl, Complex.real_smul,Complex.ofReal_inv]; field_simp [show (k:ℂ)≠0 by exact_mod_cast hk.ne']; rfl

lemma measurable_comp_smul_volume {E : Type} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {g:Body I→E}
    (hm:Measurable g) (hg:Integrable g) (s:ℝ) (hs:s≠0) : Integrable (fun x=>g (s • x)) := by
  have he : Measurable (fun x:Body I=>s • x) := by fun_prop
  have := integrable_map_measure (μ:=volume) (f:=fun x : Body I=>s • x) (g:=g) (hm.stronglyMeasurable.aestronglyMeasurable) he.aemeasurable
  rw [Measure.map_addHaar_smul _ hs] at this; exact this.mp (hg.smul_measure ENNReal.ofReal_ne_top)

lemma integrable_tilt (A:Matrix I I ℝ) (hA:A.PosDef) (r:ℝ) (hr:0<r) (g:Body I→ℂ) (hg: Measurable g) (hi:Integrable g (Poll.sweep A)) :
    Integrable (fun z=>(tilt A r z:ℂ)*g (Real.sqrt r • z)) (Poll.sweep A) := by
 have hm := (measurable_pdf A).ennreal_ofReal
 have ht := Filter.Eventually.of_forall (f:=ae volume) fun z:Body I=> ENNReal.ofReal_lt_top (r:=pdf A z)
 have hi': Integrable (fun z=>(pdf A z:ℂ)*g z) := by rw [cosh _ hA, integrable_withDensity_iff_integrable_smul' hm ht] at hi; simpa only [ENNReal.toReal_ofReal (prices ..),Complex.real_smul] using hi
 rw [cosh _ hA, integrable_withDensity_iff_integrable_smul' hm ht]
 simp only [ENNReal.toReal_ofReal (prices ..),Complex.real_smul]
 let s:=√r; have hs: s ≠ 0:= (Real.sqrt_pos.mpr hr).ne'; let W :=fun w=>(pdf A w:ℂ)*g w
 apply Integrable.congr ((measurable_comp_smul_volume (g:=W) ((Continuous.measurable Complex.continuous_ofReal|>.comp (measurable_pdf _)).mul hg) hi' s hs).const_mul ((s:ℂ)^Fintype.card I))
 refine Filter.Eventually.of_forall fun z=>?_
 dsimp [W,s]; rw [←Complex.ofReal_pow,←mul_assoc,← Complex.ofReal_mul, ←tilt_exact _ _ hr.le]; rw [mul_comm (tilt ..)]; simp only [Complex.ofReal_mul]; ring
end YM.UVExt.EnergyRay.Gaussian
