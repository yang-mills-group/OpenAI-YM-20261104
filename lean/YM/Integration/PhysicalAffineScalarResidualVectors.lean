import YM.Integration.PhysicalAffineScalarGaussianWeights
import YM.Integration.PhysicalAffineScalarRetainedSource

/-! The nonlinear physical normal equations on common raw coordinates, with
different active forests and their originally purchased inverse Grams. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarResidualVectors
open Filter Function Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalNext.Repeat.Greenbelt PhysicalAffineScalarCutResidual PhysicalAffineScalarCutWeights PhysicalAffineScalarGaussianWeights
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section Algebra
variable {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]

def loadCenter (J : Matrix α β ℝ) (C : Gaussian.Table β) (f : Gaussian.Vec α) := C *ᵥ (J.transpose *ᵥ f)

def residual (J : Matrix α β ℝ) (C : Gaussian.Table β) (f : Gaussian.Vec α) := f-J *ᵥ loadCenter J C f

def forcing (L D : Matrix α β ℝ) (H : Gaussian.Table β) (u e : Gaussian.Vec α) := e-D *ᵥ loadCenter L H u

def small (J L D : Matrix α β ℝ) (C H : Gaussian.Table β) (u e : Gaussian.Vec α) :=
  let y := forcing L D H u e
  y - J *ᵥ (C *ᵥ (J.transpose *ᵥ y+D.transpose *ᵥ residual L H u))

private theorem remaining_apply [DecidableEq ι] (M : Matrix α ι ℝ) (Q : Gaussian.Table ι)
    (f : Gaussian.Vec α) (hq : M.transpose * M = Q) :
    PhysicalAffineScalarUncut.remaining M *ᵥ f = f - M *ᵥ (Q⁻¹ *ᵥ (M.transpose *ᵥ f)) := by
  simp only [PhysicalAffineScalarUncut.remaining, Matrix.sub_mulVec, Matrix.one_mulVec,
    hq, ← Matrix.mulVec_mulVec]

private theorem on_active [DecidableEq ι] (M : Matrix α ι ℝ) (Q : Gaussian.Table ι)
    (J : Matrix α β ℝ) (E : Matrix β ι ℝ) (C : Gaussian.Table β) (f : Gaussian.Vec α)
    (hm : M = J * E) (hq : M.transpose * M = Q) (hc : E * Q⁻¹ * E.transpose = C) :
    PhysicalAffineScalarUncut.remaining M *ᵥ f = residual J C f := by
  rw [remaining_apply M Q f hq, hm, ← hc]
  simp only [residual, loadCenter, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]

private theorem reduced_active (J L D : Matrix α β ℝ) (E : Matrix β ι ℝ) (C H : Gaussian.Table ι)
    (u e : Gaussian.Vec α) :
    let y := e + (D * E) *ᵥ (-(H *ᵥ ((L * E).transpose *ᵥ u)))
    y - (J * E) *ᵥ (C *ᵥ ((J * E).transpose *ᵥ y)) -
      (J * E) *ᵥ (C *ᵥ ((D * E).transpose *ᵥ residual L (E * H * E.transpose) u)) =
      small J L D (E * C * E.transpose) (E * H * E.transpose) u e := by
  dsimp only
  simp only [small, forcing, loadCenter, Matrix.transpose_mul, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_neg, Matrix.mulVec_add, sub_eq_add_neg]
  abel
end Algebra

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)
    (F : Forest S.ratio) (q : Chi) (d : ℝ) {σ K Λ : ℝ}
local notation "A" => noHole S
local notation "W" => shots S x
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "rows" => Rows.Receipt G S
local notation "J" => ConditionalAffineForcing.rawRows T k (shorter (till x))
local notation "L" => ConditionalAffineForcing.rawRows T k all
local notation "D" => columnTail T x k
local notation "C" => covariance T k F (shorter (till x))
local notation "H" => covariance T k F all
local notation "u" => PhysicalAffineScalarUncut.offset T k
local notation "v" => shortSource T x k
local notation "e" => sourceTail T x
local notation "E" => insertion (address (G:=G) A F x)
local notation "Dc" => fun B : Coarse => Rows.move T x (V B) k W A F
local notation "Du" => PhysicalAffineScalarUncut.columns T x k F
local notation "Qc" => fun B : Coarse => Rows.gram T x (V B) k W A F
local notation "Qu" => PhysicalAffineScalarUncut.gram T x k F
local notation "ru" => PhysicalAffineScalarUncut.sourceResidual T x k F

/-- All three original residual vectors simultaneously. The first uses the
actual finite stored source, the second its prescribed full affine source,
and the last has an explicit genuine discarded factor in every monomial. -/
theorem original (Y : LinkArray G (Frozen A x F)) (hp : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high σ K Λ)
    (hQ : ∀ᶠ B : Coarse in 𝓝 0, (Qc B).PosDef ∧ (Qu B).PosDef) :
    ∀ᶠ B : Coarse in 𝓝 0, cutResidual T x k F q d Y B=residual (J B) (C B) (v B) ∧
      ru B=residual (L B) (H B) (u B) ∧
      displacement T x k F q d Y B=small (J B) (L B) (D B) (C B) (H B) (u B) (e B) := by
  filter_upwards [PhysicalAffineScalarGaussianWeights.response T x k F q d Y hp hT,
    PhysicalAffineScalarGaussianWeights.deposited T x k F hp hT,hQ] with B hR hCov hpos
  obtain ⟨hc,hu,hf⟩ := hR
  have hc' : Dc B = J B * E := hc
  have hd : columnGap T x k F B = D B * E := by
    change Dc B - Du B = _
    rw [hc', hu, ← Matrix.sub_mul]
    rfl
  have he : sourceGap T x k F q d Y B=e B := by
    change Rows.source T x (represent (decode B)) k W A F q d Y - u B = _
    rw [hf]
    have H₀ := PhysicalAffineScalarRetainedSource.full_decomposition T x k B
    ext i; have h₀ := congrFun H₀ i; simp only [Pi.sub_apply] at h₀ ⊢; linarith only [h₀]
  have h₁ : cutResidual T x k F q d Y B=residual (J B) (C B) (v B) := by
    have hr : cutResidual T x k F q d Y B = PhysicalAffineScalarUncut.remaining (Dc B)*ᵥ Rows.source T x (V B) k W A F q d Y :=
      PhysicalAffineScalarUncut.residual_projection (Dc B) _
    rw [hr,hf]
    exact on_active (Dc B) (Qc B) (J B) E (C B) (v B) hc' rfl hCov.1
  have h₂ : ru B=residual (L B) (H B) (u B) := by
    rw [PhysicalAffineScalarUncut.projected_residual]
    exact on_active (Du B) (Qu B) (L B) E (H B) (u B) hu rfl hCov.2
  refine ⟨h₁,h₂,?_⟩
  rw [PhysicalAffineScalarCutResidual.reduced T x k F q d Y B hpos.1 hpos.2]
  have hr (f : Gaussian.Vec rows) := remaining_apply (Dc B) (Qc B) f rfl
  have hcenter : PhysicalAffineScalarUncut.center T x k F B =
      -((Qu B)⁻¹ *ᵥ ((Du B).transpose *ᵥ u B)) := rfl
  rw [perturbation, forcingGap]
  change PhysicalAffineScalarUncut.remaining (Dc B) *ᵥ
      (sourceGap T x k F q d Y B + columnGap T x k F B *ᵥ PhysicalAffineScalarUncut.center T x k F B) -
      Dc B *ᵥ ((Qc B)⁻¹ *ᵥ ((columnGap T x k F B).transpose *ᵥ ru B)) = _
  rw [hr, he, hd, hcenter, h₂, hc', hu, ← hCov.1, ← hCov.2]
  exact reduced_active ..

/-- Pointwise-root scalar with its correct negative normalization before
all coarse derivatives, from this same physical exterior and true Gram. -/
theorem square (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c) (hp : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high σ K Λ) (hQ : ∀ᶠ B : Coarse in 𝓝 0, (Qc B).PosDef ∧ (Qu B).PosDef) :
    squareGap T x k F q d Y g o =ᶠ[𝓝 0] fun B =>
      (-(2*g^2)⁻¹)*∑ i : rows, if PhysicalAffineScalarComparison.rowRoot S i=o then
        small (J B) (L B) (D B) (C B) (H B) (u B) (e B) i *
          (residual (J B) (C B) (v B) i+residual (L B) (H B) (u B) i) else 0 := by
  filter_upwards [original T x k F q d Y hp hT hQ] with B hB
  rw [squareGap,Finset.mul_sum,hB.1,hB.2.1,hB.2.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

end YM.Integration.PhysicalAffineScalarResidualVectors
