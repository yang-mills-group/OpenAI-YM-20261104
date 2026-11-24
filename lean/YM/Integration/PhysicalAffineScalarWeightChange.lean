import YM.Integration.PhysicalAffineScalarGaussianWeights
import YM.Integration.PhysicalAffineScalarTreeCovariance

/-! A single changed forest in the two stationary weights. Every oriented
summand contains one ordinary covariance increment on the original fine keys. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarWeightChange
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalAffineScalarCutWeights PhysicalAffineScalarGaussianWeights
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section algebra
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
variable (J L : Matrix α β ℝ) (f u : Gaussian.Vec α) (g : ℝ)

/-- The sign is that of the variation of the residual projection. -/
def projectionChange (J : Matrix α β ℝ) (D : Gaussian.Table β) : Gaussian.Table α := -(J*D*J.transpose)

omit [Fintype α] in
private theorem project_change (C C' : Gaussian.Table β) :
    project J C'-project J C=projectionChange J (C'-C) := by
  simp only [project,projectionChange,Matrix.mul_sub,Matrix.sub_mul]
  abel

private theorem residual_change (C C' : Gaussian.Table β) (i : α) :
    (project J C' *ᵥ f) i-(project J C *ᵥ f) i=(projectionChange J (C'-C) *ᵥ f) i := by
  have h := congrArg (fun K : Gaussian.Table α => (K *ᵥ f) i) (project_change J C C')
  simpa only [Matrix.sub_mulVec,Pi.sub_apply] using h

omit [DecidableEq α] in
private theorem center_change (H H' : Gaussian.Table β) (j : β) :
    forceCenter L H' u j-forceCenter L H u j=forceCenter L (H'-H) u j := by
  simp only [forceCenter,Matrix.sub_mulVec,Pi.neg_apply,Pi.sub_apply]
  ring

def gain (C H : Gaussian.Table β) (z : α) : ℝ :=
  -((project J C *ᵥ f) z+(project L H *ᵥ u) z)/(2*g^2)

def gainChange (D E : Gaussian.Table β) (z : α) : ℝ :=
  -((projectionChange J D *ᵥ f) z+(projectionChange L E *ᵥ u) z)/(2*g^2)

private theorem gain_change (C H C' H' : Gaussian.Table β) (z : α) :
    gain J L f u g C' H' z - gain J L f u g C H z=gainChange J L f u g (C'-C) (H'-H) z := by
  rw [gainChange,←residual_change J f C C' z,←residual_change L u H H' z]
  unfold gain
  ring

def kernel (C H : Gaussian.Table β) (z i : α) (j : β) : ℝ :=
  project J C z i*forceCenter L H u j - (J*C) z j*(project L H *ᵥ u) i

/-- Four physical terms. Here D and E are the cut and full Gaussian increments. -/
def kernelChange (C H' D E : Gaussian.Table β) (z i : α) (j : β) : ℝ :=
  projectionChange J D z i*forceCenter L H' u j + project J C z i*forceCenter L E u j
  -(J*D) z j*(project L H' *ᵥ u) i - (J*C) z j*(projectionChange L E *ᵥ u) i

private theorem kernel_change (C H C' H' : Gaussian.Table β) (z i : α) (j : β) :
    kernel J L u C' H' z i j-kernel J L u C H z i j =
      kernelChange J L u C H' (C'-C) (H'-H) z i j := by
  have hp : project J C' z i-project J C z i=projectionChange J (C'-C) z i :=
    congrArg (fun A : Gaussian.Table α => A z i) (project_change J C C')
  rw [kernelChange,←hp,←center_change L u H H' j,←residual_change L u H H' i,Matrix.mul_sub]
  simp only [kernel,Matrix.sub_apply]
  ring

/-- Bilinear one-change formula at a held set of genuinely translated physical rows. -/
theorem row (C H C' H' : Gaussian.Table β) (s : Finset α) (i : α) :
    (∑ z ∈ s, gain J L f u g C' H' z * project J C' z i)
      -(∑ z ∈ s, gain J L f u g C H z * project J C z i) =
    ∑ z ∈ s, (gainChange J L f u g (C'-C) (H'-H) z * project J C' z i
      +gain J L f u g C H z * projectionChange J (C'-C) z i) := by
  rewrite [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hp : project J C' z i-project J C z i=projectionChange J (C'-C) z i :=
    congrArg (fun A : Gaussian.Table α => A z i) (project_change J C C')
  rw [←gain_change,←hp]
  ring

/-- The corresponding identity for a true signed affine column on a common raw key. -/
theorem column (C H C' H' : Gaussian.Table β) (s : Finset α) (i : α) (j : β) :
    (∑ z ∈ s, gain J L f u g C' H' z * kernel J L u C' H' z i j)
      -(∑ z ∈ s, gain J L f u g C H z * kernel J L u C H z i j) =
    ∑ z ∈ s, (gainChange J L f u g (C'-C) (H'-H) z * kernel J L u C' H' z i j
      +gain J L f u g C H z * kernelChange J L u C H' (C'-C) (H'-H) z i j) := by
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [←gain_change,←kernel_change]
  ring
end algebra

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)
    (F U : Forest S.ratio) (q : Chi) (d : ℝ) {σ K Λ : ℝ}
local notation "A" => noHole S
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "rows" => Rows.Receipt G S
local notation "short" => shorter (till x)
local notation "J" => ConditionalAffineForcing.rawRows T k short
local notation "L" => ConditionalAffineForcing.rawRows T k all
local notation "u" => PhysicalAffineScalarUncut.offset T k
local notation "f₀" => PhysicalAffineScalarCutResidual.shortSource T x k
local notation "C" => fun V : Forest S.ratio => covariance T k V short
local notation "H" => fun V : Forest S.ratio => covariance T k V all

/-- Both differences of independently observed ordinary weights, with the same
root, inputs and independently normalized original Gaussian spaces. -/
theorem original (Y : LinkArray G (Frozen A x F)) (Z : LinkArray G (Frozen A x U))
    (g : ℝ) (o : Site c) (hp : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ) :
    ∀ᶠ B : Coarse in 𝓝 0, let D := C U B-C F B; let E := H U B-H F B
      (∀ i : rows, rowWeight T x k U q d Z g o i B - rowWeight T x k F q d Y g o i B =
        ∑ z ∈ held (G:=G) (S:=S) o, (gainChange (J B) (L B) (f₀ B) (u B) g D E z * project (J B) (C U B) z i
          +gain (J B) (L B) (f₀ B) (u B) g (C F B) (H F B) z * projectionChange (J B) D z i)) ∧
      ∀ (i : rows) (j : Raw G f), columnWeight T x k U q d Z g o i j B - columnWeight T x k F q d Y g o i j B =
        ∑ z ∈ held (G:=G) (S:=S) o, (gainChange (J B) (L B) (f₀ B) (u B) g D E z * kernel (J B) (L B) (u B) (C U B) (H U B) z i j
          +gain (J B) (L B) (f₀ B) (u B) g (C F B) (H F B) z * kernelChange (J B) (L B) (u B) (C F B) (H U B) D E z i j) := by
  filter_upwards [PhysicalAffineScalarGaussianWeights.original T x k F q d Y g o hp hT,
    PhysicalAffineScalarGaussianWeights.original T x k U q d Z g o hp hT] with B hF hU
  constructor
  · intro i
    exact (congrArg₂ (fun a b : ℝ => a-b) (hU.1 i) (hF.1 i)).trans
      (row (J B) (L B) (f₀ B) (u B) g (C F B) (H F B) (C U B) (H U B) (held (G:=G) (S:=S) o) i)
  · intro i j
    exact (congrArg₂ (fun a b : ℝ => a-b) (hU.2 i j) (hF.2 i j)).trans
      (column (J B) (L B) (f₀ B) (u B) g (C F B) (H F B) (C U B) (H U B) (held (G:=G) (S:=S) o) i j)

/-- True primary Gram positivity identifies the computed active covariance germ
with the one-tree quantity priced by `PhysicalAffineScalarTreeCovariance`. -/
theorem observed {b a : ℝ} (hs : 0<b) (ha : 0≤a) (hW : Sheet T.up b a)
    (he : Bid.Larger (G:=G) S) (r : Admit) :
    covariance T k F r =ᶠ[𝓝 (0:Coarse)] PhysicalAffineScalarTreeCovariance.observed F k T.high T.up r := by
  have hh := FreeResolvent.Affine.knows F k hs ha hW he T.high 1 r
  have hd := hh.gap.unit_det (headGap_pos G S.patch S.kernel T.high)
  have hc := (continuous_id.matrix_det.continuousAt.comp hh.smooth.continuousAt).eventually_ne hd.ne_zero
  filter_upwards [hc] with B hB
  exact spectral T k F r B (IsUnit.mk0 _ hB)

/-- The ordinary two-sided summed Schur fee of the authentic deposited kernel,
with all independent field legs and either of the two actual path selections. -/
theorem covariance_ordinary {b a : ℝ} (hs : 0<b) (ha : 0≤a) (hW : Sheet T.up b a)
    (he : Bid.Larger (G:=G) S) (r : Admit) (n : ℕ) :
    let w := width G S.patch S.kernel T.high n a b
    Bundle (ray G c) (FreeResolvent.Mark.positions (native c) hearth w) (native c) (home S) (home S)
      (covariance T k F r) 0 n (4*(n+1:ℕ)*w) (earnings G S.patch S.kernel T.high n a b+1) := by
  intro w
  exact (PhysicalAffineScalarTreeCovariance.ordinary hs ha hW he (n:=n) (t:=k) (p:=T.high) F r).glue
    (observed T k F hs ha hW he r).symm

/-- Both physically selected ordinary inverse kernels pay the same native endpoint
fee for a changed tree, with a single erased-key charge only at order zero. -/
theorem covariance_price {b a : ℝ} (hs : 0<b) (ha : 0≤a) (hW : Sheet T.up b a)
    (he : Bid.Larger (G:=G) S) {tag : Site c} (hFU : changed S F U tag) (r : Admit)
    {n : ℕ} (l : List (raw G c)) (hl : l.length<n) :
    let w := width G S.patch S.kernel T.high n a b
    FreeResolvent.Lever.Here (ray G c) (native c) (home S) hearth w (4*(n+1:ℕ)*w) tag l
      (earnings G S.patch S.kernel T.high n a b + if l=[] then 1 else 0)
      (covariance T k F r) (covariance T k U r) := by
  intro w
  have hF := identical (ray G c) (observed T k F hs ha hW he r) l
  have hU := identical (ray G c) (observed T k U hs ha hW he r) l
  constructor
  intro i j
  dsimp only
  rw [hF,hU]
  by_cases hz : l=[]
  · subst l
    simpa using (PhysicalAffineScalarTreeCovariance.flat hs ha hW he (t:=k) (p:=T.high) hFU r hl).test i j
  · simpa [hz] using (PhysicalAffineScalarTreeCovariance.positive hs ha hW he (t:=k) (p:=T.high) hFU r l hz hl).test i j

end YM.Integration.PhysicalAffineScalarWeightChange
