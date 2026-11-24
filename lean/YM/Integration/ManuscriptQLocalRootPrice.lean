import YM.Integration.ManuscriptQLocalRootWeights

/-! The rooted one-tag mixed square price on the original Run. The small
inputs are its actual two discarded kernels. Each independent field sublist
occurs once on one side of the native finite Leibniz expansion. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalRootPrice
open Function Filter Matrix Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree Pressure
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Pressure.Testing Pressure.Stores
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato Progress.DirectedRecipe PhysicalAffineScalarCutWeights
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I τ : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "Coarse" => Gaussian.Vec (Raw G (R.family.side d.level d.period))
local notation "c₀" => R.family.side d.level d.period
local notation "f₀" => R.family.side (d.level+1) d.period
local notation "rows" => Rows.Receipt G S
local notation "atoms" => rows ⊕ (rows × Raw G f₀)
variable (k : (R.family.path.levels.clock.op d.level d.period).Choices) (q : Chi) (b : ℝ) (tag : Site (R.family.side d.level d.period))
    (F' : {U : Forest (R.family.path.levels.clock.op d.level d.period).ratio // changed (R.family.path.levels.clock.op d.level d.period) d.forest U tag})
    (Y : LinkArray G (Frozen (noHole (R.family.path.levels.clock.op d.level d.period)) (R.alloy.B.a.clock.hatBeta d.level) d.forest)) (Y' : LinkArray G (Frozen (noHole (R.family.path.levels.clock.op d.level d.period)) (R.alloy.B.a.clock.hatBeta d.level) F'.val)) (g : ℝ) (o : Site (R.family.side d.level d.period))

/-- Values of the actual removed source or Jacobian, indexed independently
of the chosen root, the actual tree and the charged insertion. -/
def input (a : atoms) (B : Coarse) : ℝ := a.elim (sourceTail T θ B)
  (fun z => columnTail T θ k B z.1 z.2)

/-- All the changed-root information is carried by the two physically
computed coefficient weights on the same raw site and color indices. -/
def weight (a : atoms) (B : Coarse) : ℝ := a.elim (fun z => rowWeight T θ k F'.val q b Y' g o z B-
  rowWeight T θ k d.forest q b Y g o z B) (fun z => columnWeight T θ k F'.val q b Y' g o z.1 z.2 B-
    columnWeight T θ k d.forest q b Y g o z.1 z.2 B)

def error (B : Coarse) : ℝ := (PhysicalAffineScalarJets.actualRoot T θ k A F'.val q b Y' g o B -
    PhysicalAffineScalarJets.actualRoot T θ k A d.forest q b Y g o B) -
    (PhysicalAffineScalarUncut.scalarAt T θ k F'.val g o B - PhysicalAffineScalarUncut.scalarAt T θ k d.forest g o B) -
    (PhysicalAffineScalarCutResidual.logGap T θ k F'.val o B - PhysicalAffineScalarCutResidual.logGap T θ k d.forest o B)

local notation "f" => input R d k
local notation "W" => weight R d k q b tag F' Y Y' g o
local notation "Err" => error R d k q b tag F' Y Y' g o

omit [Fintype I] in
theorem identified : Err =ᶠ[𝓝 0] fun B : Coarse => ∑ a : atoms, f a B*W a B := by
  filter_upwards [ManuscriptQLocalRootWeights.original R d k q b tag F' Y Y' g o] with B hB
  unfold error
  rw [hB]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,input,weight]
  abel

omit [Fintype I] in
/-- The common exponential price is supplied only for genuine removed
raw input coefficients. The other factors below are computed jets of the
actual changed Gaussian weights, with every independent sublist retained. -/
theorem original (v : τ → Coarse) (l : List τ) (pGeo κ M : ℝ) (cap : atoms → List τ → ℝ)
    (hf : ∀ a : atoms, ContDiffAt ℝ l.length (f a) 0) (hw : ∀ a : atoms, ContDiffAt ℝ l.length (W a) 0)
    (paid : ∀ (a : atoms) (s : List τ), s.length ≤ l.length →
      |jet v (f a) s 0| ≤ (pGeo*Real.exp (-κ*M))*cap a s) :
    |jet v Err l 0| ≤ (pGeo*Real.exp (-κ*M)) *
      ∑ a : atoms, ∑ m : Masks l, cap a (lo l m) * |jet v (W a) (hi l m) 0| := by
  let t := pGeo*Real.exp (-κ*M)
  let h (a : atoms) := fun B : Coarse => f a B*W a B
  have he : jet v Err l 0 = jet v (fun B : Coarse => ∑ a : atoms, h a B) l 0 := by
    change iteratedFDeriv ℝ l.length _ 0 _ = iteratedFDeriv ℝ l.length _ 0 _
    rw [((identified R d k q b tag F' Y Y' g o).iteratedFDeriv (𝕜:=ℝ) l.length).self_of_nhds]
  have hp (a : atoms) : |jet v (h a) l 0| ≤ ∑ m : Masks l,
      (t*cap a (lo l m))*|jet v (W a) (hi l m) 0| := by
    have hL := leibniz v (ContinuousLinearMap.mul ℝ ℝ) l (hf a) (hw a)
    change jet v (h a) l 0 = ∑ m : Masks l, jet v (f a) (lo l m) 0 * jet v (W a) (hi l m) 0 at hL
    rw [hL]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (paid a _ (by have := lengths l m; omega)) (abs_nonneg _)
  rw [he,jet_sum v l Finset.univ h (fun a _ => (hf a).mul (hw a))]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a : atoms, ∑ m : Masks l, (t*cap a (lo l m))*|jet v (W a) (hi l m) 0| := Finset.sum_le_sum fun a _ => hp a
    _ = _ := by simp only [Finset.mul_sum,mul_assoc,t]

end YM.Integration.ManuscriptQLocalRootPrice
