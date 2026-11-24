import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.License

/-! Stationary extraction on the affine chart of the original marked sector.
The chart uses the actual curved derivatives of the full predictor and of the
plaquette curvature.  The flat determinant stays in its own conditional weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarComparison

open Function Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section determinant
variable {G : Gauge} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Same Gaussian chart and coupling on both sides of the conditional log. -/
theorem chart_log_ratio {C C₀ : Gaussian.Table (ι × G.ColorIndex)} {g : ℝ}
    (hC : C.PosDef) (h₀ : C₀.PosDef) (hg : 0<g) :
    Real.log (chartCost C g / chartCost C₀ g) =
      (Real.log C.det - Real.log C₀.det)/2 := by
  let v : ℝ := Real.sqrt (2*Real.pi*g^2) ^ Fintype.card (ι × G.ColorIndex)
  have hv : 0 < v := by unfold v; positivity
  have h₁ := Real.sqrt_pos.mpr hC.det_pos
  have h₂ := Real.sqrt_pos.mpr h₀.det_pos
  change Real.log ((v * Real.sqrt C.det)/(v * Real.sqrt C₀.det)) = _
  rw [Real.log_div (mul_pos hv h₁).ne' (mul_pos hv h₂).ne',
    Real.log_mul hv.ne' h₁.ne',Real.log_mul hv.ne' h₂.ne',
    Real.log_sqrt hC.det_pos.le,Real.log_sqrt h₀.det_pos.le]
  ring

/-- The chosen positive Gaussian's normalization cancels its own determinant.
The scale of every active coordinate survives the density change. -/
theorem chart_density {C : Gaussian.Table (ι × G.ColorIndex)} {g : ℝ}
    (hC : C.PosDef) (hg : 0<g) (z : Prices G ι) :
    chartCost C g * ratio C z * Real.exp (force C z/2) =
      g ^ Fintype.card (ι × G.ColorIndex) := by
  rw [chartCost_eq C hg,ratio]
  have hz : Real.exp (-(force C z)/2) * Real.exp (force C z/2)=1 := by
    rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
  calc
    _ = g ^ Fintype.card (ι × G.ColorIndex) *
        (coat C * (coat C)⁻¹) * (Real.exp (-(force C z)/2) * Real.exp (force C z/2)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (coat_pos hC).ne',hz]; ring
end determinant

section physical
variable {G : Gauge} {c f : Side} {S : StepData c f}
  (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (W : Stencils S)
  (A : Stores S) (F : Forest S.ratio) (q : Chi) (d : ℝ)
  (Y : LinkArray G (Frozen A x F))
local notation "H" => Rows.gram T x V k W A F
local notation "jᵣ" => Rows.blame T x V k W A F q d Y
local notation "entry" => Rows.direct T x V k W A F q d Y

/-- Each signed plaquette row and each signed predictor row has its physical
translation root. The color index is never contracted with this root. -/
def rowRoot (S : StepData c f) (i : Rows.Receipt G S) : Site c :=
  i.1.1.act (i.1.2.elim (fun t : Twin f => S.ratio.parent t.1.1) (fun b : Bond c => b.1))

def rowSquare (m : Prices G (Active A x F)) (g : ℝ) (i : Rows.Receipt G S) : ℝ :=
  -(entry m i)^2/(2*g^2)

def stationary : Prices G (Active A x F) := -(H⁻¹ *ᵥ jᵣ)

theorem normal (hH : (H).PosDef) : H *ᵥ stationary T x V k W A F q d Y + jᵣ = 0 := by
  unfold stationary
  rw [Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hH.det_pos.ne'),
    Matrix.one_mulVec,neg_add_cancel]

/-- Rootwise the scalar is the squared affine residual at the indicated
center.  Grouping by site happens only after the signed row is retained. -/
theorem rooted_square (m : Prices G (Active A x F)) (g : ℝ) :
    -Rows.guide T x V k W A F q d Y m/g^2 =
      ∑ a : Site c, ∑ i : Rows.Receipt G S, if rowRoot S i = a then
        rowSquare T x V k W A F q d Y m g i else 0 := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold Rows.guide rowSquare dotProduct
  simp only [sq,← Finset.sum_div,Finset.sum_neg_distrib]
  ring

/-- The particular chart determinant is compared relative to the original
conditional flat chart.  The full residual, linear correction and quadratic
correction all use the same original affine row and the same Gaussian. -/
theorem decomposition (C C₀ : Gaussian.Table (Rows.In (G:=G) x A F)) (hC : C.PosDef) (h₀ : C₀.PosDef)
    (m z : Prices G (Active A x F)) {g : ℝ} (hg : 0<g) :
    Real.log (chartCost C g / chartCost C₀ g) +
        Rows.adjustment T x V k W A F q d Y C m g z =
      (Real.log C.det-Real.log C₀.det)/2 +
      (∑ a : Site c, ∑ i : Rows.Receipt G S, if rowRoot S i=a then
        rowSquare T x V k W A F q d Y m g i else 0) +
      (Rows.eta T x V k W A F q d Y m g ⬝ᵥ z) +
      (z ⬝ᵥ ((C⁻¹-H) *ᵥ z))/2 := by
  rw [chart_log_ratio hC h₀ hg,Rows.adjustment,← rooted_square]
  ring

/-- This is the manuscript's full stationary Gaussian scalar including the
sign of the paired logarithm in the density. No component is removed by the
quiet denominator at a fixed tree. -/
theorem stationary_scalar (H₀ : Gaussian.Table (Rows.In (G:=G) x A F))
    (h₀ : H₀.PosDef) (hH : (H).PosDef) {g : ℝ} (hg : 0<g)
    (z : Prices G (Active A x F)) :
    let m := stationary T x V k W A F q d Y
    Real.log (chartCost H⁻¹ g / chartCost H₀⁻¹ g) +
        Rows.adjustment T x V k W A F q d Y H⁻¹ m g z =
      (Real.log H₀.det-Real.log (H).det)/2 +
        ∑ a : Site c, ∑ i : Rows.Receipt G S, if rowRoot S i=a then
          rowSquare T x V k W A F q d Y m g i else 0 := by
  intro m
  rw [decomposition T x V k W A F q d Y H⁻¹ H₀⁻¹ hH.inv h₀.inv m z hg]
  have hNormal : H *ᵥ m + jᵣ=0 := normal T x V k W A F q d Y hH
  simp only [Rows.eta,hNormal,smul_zero,zero_dotProduct,add_zero,
    Matrix.nonsing_inv_nonsing_inv _ (IsUnit.mk0 _ hH.det_pos.ne'),sub_self,
    Matrix.zero_mulVec,dotProduct_zero,zero_div,Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv,Real.log_inv]
  ring
end physical

section density
variable {G : Gauge} {c f : Side} {S : StepData c f} {w σ ω₀ Λ : ℝ} {o : Clip}
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
  (A : Stores S) (R : Rep G f) (W : Stencils S) (F : Forest S.ratio)
  (D : Allocation G S x w) (q : Chi) (J : ChartRatio G) (d : ℝ)

/-- Pointwise on the same frozen Haar field and material fine field, the
paired determinant, full curved affine action and interaction give back the
original marked integrand with its physical chart Jacobian.  Arbitrary
Banach-valued marked columns, including the quiet column, use this identity. -/
theorem marked_density (hT : T.up.Bounds o σ ω₀ Λ) (hβ : 0<R.beta)
    (C : Gaussian.Table (Rows.In (G:=G) x A F)) (hC : C.PosDef)
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (u : Config G f → B) (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) :
    (Marked.outside T x V A R F J C * ratio C z) •
      Marked.ink T x V k A R W F D q J d C m u Y z =
    (sieve T R.beta x V * J.scale ^ Fintype.card (Active A x F) *
      coupling R.beta ^ Fintype.card (Rows.In (G:=G) x A F)) •
      regularized D A F V k q J d (Marked.dress T x V k A R u) Y
        (displaced (m Y) (coupling R.beta) z) := by
  let a := sieve T R.beta x V * J.scale ^ Fintype.card (Active A x F)
  have h := Marked.ink_regularized T x V k A R W F D q J d C m hT hβ u Y z
  have hc := chart_density hC (coupling_pos hβ) z
  have hMult : Marked.outside T x V A R F J C * ratio C z =
      (a * (chartCost C (coupling R.beta) * ratio C z)) * prefactor S G R.beta := by
    unfold Marked.outside a; ring
  rw [hMult,mul_smul,h,smul_smul]
  rw [mul_assoc a, hc]

/-- All chart constants dependent on the original tree stay inside this
conditional equality. The two references are evaluated at the same material
field before summing or normalizing any marked columns. -/
theorem same_material (hT : T.up.Bounds o σ ω₀ Λ) (hβ : 0<R.beta)
    (C C' : Gaussian.Table (Rows.In (G:=G) x A F)) (hC : C.PosDef) (hC' : C'.PosDef)
    (m m' : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (u : Config G f → B) (Y : LinkArray G (Frozen A x F)) (z z' : Prices G (Active A x F))
    (h : m Y + coupling R.beta • z = m' Y + coupling R.beta • z') :
    (Marked.outside T x V A R F J C * ratio C z) •
      Marked.ink T x V k A R W F D q J d C m u Y z =
    (Marked.outside T x V A R F J C' * ratio C' z') •
      Marked.ink T x V k A R W F D q J d C' m' u Y z' := by
  rw [marked_density T x V k A R W F D q J d hT hβ C hC,
    marked_density T x V k A R W F D q J d hT hβ C' hC']
  simp only [displaced,h]
end density
end YM.Integration.PhysicalAffineScalarComparison
end
