import YM.Integration.PhysicalAffineScalarOrdinaryColumns
import YM.Integration.PhysicalAffineScalarWeightChange

/-! All ordinary factors appearing in the translation-rooted stationary
square have genuine finite mixed-field germs on the original no-hole stage. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarWeightRegularity
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalAffineScalarCutWeights PhysicalAffineScalarGaussianWeights PhysicalAffineScalarCutResidual
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section entries
variable {E a b c : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Entries (n : ℕ) (D : E→Matrix a b ℝ) := ∀ i j, ContDiffAt ℝ n (fun B => D B i j) 0
def Values (n : ℕ) (f : E→a→ℝ) := ∀ i, ContDiffAt ℝ n (fun B => f B i) 0

private theorem multiply [Fintype b] {n : ℕ} {D : E→Matrix a b ℝ} {C : E→Matrix b c ℝ}
    (hD : Entries n D) (hC : Entries n C) : Entries n (fun B => D B*C B) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ => (hD i k).mul (hC k j)

private theorem act [Fintype b] {n : ℕ} {D : E→Matrix a b ℝ} {f : E→b→ℝ}
    (hD : Entries n D) (hf : Values n f) : Values n (fun B => D B *ᵥ f B) := by
  intro i
  change ContDiffAt ℝ n (fun B => ∑ j, D B i j*f B j) 0
  exact ContDiffAt.sum fun j _ => (hD i j).mul (hf j)

private theorem projection [Fintype b] [DecidableEq a] {n : ℕ} {D : E→Matrix a b ℝ} {C : E→Matrix b b ℝ}
    (hD : Entries n D) (hC : Entries n C) : Entries n (fun B => project (D B) (C B)) := by
  have ht : Entries n (fun B => (D B).transpose) := fun i j => hD j i
  have h := multiply (multiply hD hC) ht
  intro i j
  exact contDiffAt_const.sub (h i j)

private theorem center [Fintype a] [Fintype b] {n : ℕ} {D : E→Matrix a b ℝ}
    {C : E→Matrix b b ℝ} {u : E→a→ℝ} (hD : Entries n D) (hC : Entries n C) (hu : Values n u) :
    Values n (fun B => forceCenter (D B) (C B) (u B)) := by
  have ht : Entries n (fun B => (D B).transpose) := fun i j => hD j i
  intro i
  exact ((act hC (act ht hu)) i).neg
end entries

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)
local notation "A" => noHole S
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "rows" => Rows.Receipt G S
local notation "short" => shorter (till x)
local notation "J" => ConditionalAffineForcing.rawRows T k short
local notation "L" => ConditionalAffineForcing.rawRows T k all
local notation "u" => PhysicalAffineScalarUncut.offset T k
local notation "f₀" => shortSource T x k

/-- Both explicitly computed polynomial response weights on the same raw-coordinate Gaussian. -/
theorem raw (n : ℕ) (g : ℝ) (o : Site c) (C H : Coarse→Gaussian.Table (Raw G f))
    (hJ : Entries n J) (hL : Entries n L) (hC : Entries n C) (hH : Entries n H)
    (hv : Values n f₀) (hu : Values n u) :
    (∀ i, ContDiffAt ℝ n (fun B => rawRow T x k g o i B (C B) (H B)) 0) ∧
    ∀ i j, ContDiffAt ℝ n (fun B => rawColumn T x k g o i j B (C B) (H B)) 0 := by
  have hP := projection hJ hC
  have hR := projection hL hH
  have hc := act hP hv
  have hr := act hR hu
  have hm := center hL hH hu
  have hJC := multiply hJ hC
  let gain := fun B z => -((project (J B) (C B) *ᵥ f₀ B) z + (project (L B) (H B) *ᵥ u B) z)/(2*g^2)
  have hg (z : rows) : ContDiffAt ℝ n (fun B => gain B z) 0 := ((hc z).add (hr z)).neg.div_const _
  constructor
  · intro i
    exact ContDiffAt.sum fun z _ => (hg z).mul (hP z i)
  · intro i j
    exact ContDiffAt.sum fun z _ => (hg z).mul (((hP z i).mul (hm j)).sub ((hJC z j).mul (hr i)))

/-- Original physically stored weights. All data bounds below are the
authentic raw path sheet, actual funded stage and already priced sources. -/
theorem original (F : Forest S.ratio) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c)
    {a b σ K Λ : ℝ} (hp : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ)
    (hs : 0<b) (ha : 0≤a) (hW : Sheet T.up b a) (hc : 1<c.val) (he : Bid.Larger (G:=G) S)
    (n : ℕ) (hv : Values n f₀) (hu : Values n u) :
    (∀ i, ContDiffAt ℝ n (rowWeight T x k F q d Y g o i) 0) ∧
    ∀ i j, ContDiffAt ℝ n (columnWeight T x k F q d Y g o i j) 0 := by
  let C := covariance T k F short
  let H := covariance T k F all
  have hG (r : Admit) : Entries n (covariance T k F r) := fun i j => (evaluate i j).contDiff.contDiffAt.comp 0
    (PhysicalAffineScalarWeightChange.covariance_ordinary T k F hs ha hW he r n).smooth
  have hh := raw T x k n g o C H (PhysicalAffineScalarOrdinaryColumns.smooth T k short hp hc hs ha hW n)
    (PhysicalAffineScalarOrdinaryColumns.smooth T k all hp hc hs ha hW n) (hG short) (hG all) hv hu
  have hz := PhysicalAffineScalarGaussianWeights.original T x k F q d Y g o hp hT
  exact ⟨fun i => (hh.1 i).congr_of_eventuallyEq (hz.mono fun _ he' => he'.1 i),
    fun i j => (hh.2 i j).congr_of_eventuallyEq (hz.mono fun _ he' => he'.2 i j)⟩

end YM.Integration.PhysicalAffineScalarWeightRegularity
