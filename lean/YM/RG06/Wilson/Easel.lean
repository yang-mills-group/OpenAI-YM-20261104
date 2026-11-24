import YM.RG06.Series.Taylor
import YM.UVExt.PathJet
/-!
# Matrix and color polynomial compiler for Wilson link stencils

`Easel G V` is matrices over complex polynomials in **real** variables V. Star
of a variable is itself. Positive link log scale `r • A` in native units. `G.mat`
and `G.colorMat` (not the defining trace normalized by hand) used throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06
namespace WilsonCompiler
open Function Gauge MvPolynomial GSeries
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {V : Type*}
abbrev Pigment (V : Type*) := MvPolynomial V ℂ
abbrev Easel (G : Gauge) (V : Type*) := Matrix (Fin G.repDim) (Fin G.repDim) (Pigment V)


/-- Evaluate at real data. -/
def tone (v : V → ℝ) : Pigment V →+* ℂ := MvPolynomial.eval (fun i => (v i : ℂ))
def picture (v : V → ℝ) : Easel G V →+* G.Mat := (tone v).mapMatrix

/-- Lift coefficient conjugation (not hermitian-conjugating the variable). -/
def conjugateP (V : Type*) : Pigment V →+* Pigment V := MvPolynomial.map (starRingEnd _)

@[simp] lemma picture_apply (v : V → ℝ) (Z : Easel G V) (i j) :
    picture v Z i j = tone v (Z i j) := rfl
@[simp] lemma tone_C (v : V → ℝ) (a : ℂ) : tone v (MvPolynomial.C a) = a := MvPolynomial.eval_C ..
@[simp] lemma tone_X (v : V → ℝ) (a : V) : tone v (MvPolynomial.X a) = (v a : ℝ) := MvPolynomial.eval_X ..

@[simp] lemma tone_conjugate (v : V → ℝ) (p : Pigment V) : tone v (conjugateP V p) = star (tone v p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [conjugateP]
  | add a b ha hb => rw [map_add,map_add,map_add,ha,hb,star_add] -- namespace conflict?
  | mul_X p i hp => rw [_root_.map_mul,_root_.map_mul,hp,_root_.map_mul]; simp [conjugateP]

/-- Noncommuting matrix series, cp. the ordered `travel`. -/
abbrev Animation (G : Gauge) (V : Type*) := PowerSeries (Easel G V)

def soundtrack (v : V → ℝ) : Animation G V →+* PowerSeries G.Mat :=
  PowerSeries.map (picture v)

def develop (v : V → ℝ) : PowerSeries (Pigment V) →+* PowerSeries ℂ :=
  PowerSeries.map (tone v)

@[simp] lemma soundtrack_coeff (v : V→ℝ) (X : Animation G V) (k : ℕ) :
    PowerSeries.coeff k (soundtrack v X) = picture v (PowerSeries.coeff k X) :=
  PowerSeries.coeff_map ..

@[simp] lemma develop_coeff (v : V→ℝ) (X : PowerSeries (Pigment V)) (k : ℕ) :
    PowerSeries.coeff k (develop v X) = tone v (PowerSeries.coeff k X) :=
  PowerSeries.coeff_map ..

/-- `exp(r m)` ordinary formal series. Complex scalars explicitly as ℝ
complexification. -/
def logRoll (m : Easel G V) : Animation G V := PowerSeries.mk fun k =>
  (MvPolynomial.C (σ:=V) (R:=ℂ) (k.factorial : ℂ)⁻¹) • m^k

@[simp] lemma picture_C_smul (v : V → ℝ) (r : ℝ) (Q : Easel G V) :
    picture v (MvPolynomial.C (σ:=V) (r:ℂ) • Q) = r • picture v Q := by
  ext1 i j
  rw [picture_apply, Matrix.smul_apply, smul_eq_mul, _root_.map_mul, tone_C, Matrix.smul_apply,picture_apply]
  rw [Complex.real_smul]

/-- Identify exp coefficients with the real link exponential (including leading identity).
Use only when matched to the Lie matrix; no complex-group statement. -/
theorem link_beat (v : V → ℝ) (m : Easel G V) (b : G.Color)
    (h : picture v m = G.colorMat b) :
    Garnish 0 (fun r : ℝ => G.mat (G.lieExp (r • b))) (soundtrack v (logRoll m)) := by
  refine ⟨G.exp_jet.contDiffAt.comp (f:=fun r:ℝ => r • b) (0:ℝ) ((contDiffAt_id (𝕜:=ℝ)).smul contDiffAt_const) |>.of_le le_top,?_⟩
  ext1 k
  rw [soundtrack_coeff,logRoll,PowerSeries.coeff_mk,assembler_coeff,offer, YM.UVExt.Paths.ray_deriv]
  have he : (k.factorial : ℂ)⁻¹ = (((k.factorial : ℝ)⁻¹:ℝ):ℂ) := by simp
  rw [he,picture_C_smul,_root_.map_pow,h]; simp

/-- Generate the color matrix polynomial when V contains coordinates of a color.
The basis is physical orthonormal EuclideanSpace singles, yielding G.colorScale
in the matrix entries as required. -/
private def palette (G : Gauge) (i : G.ColorIndex) : G.Color := EuclideanSpace.single i 1

def colorTube (G : Gauge) (v : G.ColorIndex → Pigment V) : Easel G V :=
  Matrix.of fun i j => ∑ c : G.ColorIndex, v c * MvPolynomial.C (G.colorMat (palette G c) i j)

private theorem palette_sum (a : G.Color) : ∑ c : G.ColorIndex, a c • palette G c = a := by
  ext i
  simp [palette,Pi.single_apply,mul_ite]

@[simp] theorem colorTube_eval (u : V → ℝ) (a : G.Color) (v : G.ColorIndex → Pigment V)
    (h : ∀ i,tone u (v i) = (a i : ℂ)) : picture u (colorTube G v) = G.colorMat a := by
  -- don't rewrite inside coordinates also
  have he : G.colorMat a = ∑ c, a c • G.colorMat (palette G c) := by
    conv_lhs => arg 2; rw [← palette_sum a]
    rw [_root_.map_sum]; simp only [_root_.map_smul]
  rw [he]; ext1 i j
  simp only [picture_apply,colorTube, Matrix.of_apply,_root_.map_sum,_root_.map_mul,h,tone_C,
    Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]

-- interpret one (optionally conjugated) entry read.
def frameP (m : Animation G V) (i j : Fin G.repDim) (c : Bool) : PowerSeries (Pigment V) :=
  PowerSeries.mk fun k =>
    let a := PowerSeries.coeff k m i j
    if c then conjugateP V a else a

private def tinter (c : Bool) (i j : Fin G.repDim) : G.Mat →L[ℝ] ℂ :=
 LinearMap.toContinuousLinearMap {
   toFun := fun m => if c then star (m i j) else m i j
   map_add' := fun A B => by split <;> simp_all
   map_smul' := fun r A => by split <;> simp_all [Complex.real_smul,mul_comm] }

theorem frame_match (u : V → ℝ) (c : Bool) (i j : Fin G.repDim) {t : ℝ} {f : ℝ → G.Mat} {P : Animation G V}
    (h : Garnish t f (soundtrack u P)) :
    Garnish t (fun r => if c then star (f r i j) else f r i j) (develop u (frameP P i j c)) := by
  have he : develop u (frameP P i j c) = reCoeff (tinter c i j).toLinearMap (soundtrack u P) := by
    ext1 k; rw [develop_coeff,frameP,PowerSeries.coeff_mk,coeff_reCoeff,soundtrack_coeff]
    cases c <;> simp [picture_apply, tone_conjugate, tinter]
  rw [he]; exact h.linear (tinter c i j)


/-- Real and imaginary part recovered as complex scalar series at real data,
using `frameP`. -/
def reFrame (m : Animation G V) (i j : Fin G.repDim) :=
  PowerSeries.C (MvPolynomial.C (σ:=V) ((2:ℂ)⁻¹)) * (frameP m i j false + frameP m i j true)
def imFrame (m : Animation G V) (i j : Fin G.repDim) :=
  PowerSeries.C (MvPolynomial.C (σ:=V) ((2*Complex.I)⁻¹)) * (frameP m i j false - frameP m i j true)

theorem reFrame_match (u : V → ℝ) (i j : Fin G.repDim) {t : ℝ} {f : ℝ → G.Mat} {P : Animation G V}
    (h : Garnish t f (soundtrack u P)) :
    Garnish t (fun r => ((f r i j).re:ℂ)) (develop u (reFrame P i j)) := by
  let a := frame_match u false i j h
  let b := frame_match u true i j h
  have e z : (2:ℂ)⁻¹ * (z + star z) = (z.re : ℂ) := by rw [Complex.re_eq_add_conj, div_eq_inv_mul]; rfl
  unfold reFrame develop
  rw [_root_.map_mul,_root_.map_add, PowerSeries.map_C,tone_C]
  have ht := (Garnish.C_mul (2:ℂ)⁻¹ (a.add b))
  change Garnish t (fun r => (2:ℂ)⁻¹ * (f r i j+star (f r i j))) _ at ht
  simp_rw [e] at ht
  exact ht

theorem imFrame_match (u : V → ℝ) (i j : Fin G.repDim) {t : ℝ} {f : ℝ → G.Mat} {P : Animation G V}
    (h : Garnish t f (soundtrack u P)) :
    Garnish t (fun r => ((f r i j).im:ℂ)) (develop u (imFrame P i j)) := by
  let a := frame_match u false i j h
  let b := frame_match u true i j h
  have e (z:ℂ) : (2*Complex.I)⁻¹ * (z-star z) = (z.im : ℂ) := by rw [Complex.im_eq_sub_conj,div_eq_inv_mul]; rfl
  unfold imFrame develop
  rw [_root_.map_mul,_root_.map_sub, PowerSeries.map_C,tone_C]
  have ht := Garnish.C_mul ((2*Complex.I:ℂ)⁻¹) (a.sub b)
  change Garnish t (fun r => ((2*Complex.I:ℂ)⁻¹) * (f r i j - star (f r i j))) _ at ht
  simp_rw [e] at ht
  exact ht

abbrev tray {V : Type*} (r : ℂ) : PowerSeries (Pigment V) := PowerSeries.C (MvPolynomial.C r)

def extract (L : G.Mat →ₗ[ℝ] ℂ) (m : Animation G V) : PowerSeries (Pigment V) :=
  ∑ i : Fin G.repDim, ∑ j : Fin G.repDim,
    (reFrame m i j * tray (L (Matrix.single i j 1)) + imFrame m i j * tray (L (Matrix.single i j Complex.I)))

theorem extract_match (u : V → ℝ) (L : G.Mat →ₗ[ℝ] ℂ) {t : ℝ} {f : ℝ → G.Mat} {P : Animation G V}
    (h : Garnish t f (soundtrack u P)) : Garnish t (L ∘ f) (develop u (extract L P)) := by
  have e (M:G.Mat) : L M = ∑ i : Fin G.repDim, ∑ j : Fin G.repDim,
      (((M i j).re:ℂ) * L (Matrix.single i j 1) + ((M i j).im : ℂ) * L (Matrix.single i j Complex.I)) := by
    conv_lhs=> rw [Matrix.matrix_eq_sum_single M]
    simp only [_root_.map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hp (z : ℂ) : (Matrix.single (n:=Fin G.repDim) (m:=Fin G.repDim) i j z) = z.re • Matrix.single i j (1:ℂ) + z.im • Matrix.single i j Complex.I := by
      rw [Matrix.smul_single,Matrix.smul_single,←Matrix.single_add]; simp [Complex.real_smul]
    rw [hp,_root_.map_add,_root_.map_smul,_root_.map_smul]; simp [Complex.real_smul]
  unfold extract
  simp only [_root_.map_sum,_root_.map_add,_root_.map_mul,Function.comp_def]
  conv => arg 2; ext r; rw [e]
  apply Garnish.fun_sum
  intro i _
  apply Garnish.fun_sum
  intro j _
  have ht := ((reFrame_match u i j h).mul_C (L (Matrix.single i j 1))).add
    ((imFrame_match u i j h).mul_C (L (Matrix.single i j Complex.I)))
  simp only [develop,tray,PowerSeries.map_C,tone_C]
  exact ht
end WilsonCompiler
end YM.RG06
