import YM.Integration.ManuscriptQLocalStationaryGeometry
import YM.Integration.ManuscriptQLocalScalarSourcePurchase
import YM.Integration.PhysicalAffineScalarWeightRegularity
import YM.Integration.PhysicalAffineScalarInputBudget
import YM.Integration.ManuscriptQLocalRootPrice

/-! Measured versus prescribed rooted stationary square on one chosen Run.
The partial log determinant is retained separately, at its own true roots.
The right side reports the genuine changed Gaussian-weight contraction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalPaidRootSquare
open Function Filter Matrix Marker Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarCutWeights PhysicalAffineScalarCutResidual PhysicalAffineScalarWeightRegularity
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "c₀" => R.family.side d.level d.period
local notation "f₀" => R.family.side (d.level+1) d.period
local notation "Coarse" => Gaussian.Vec (Raw G c₀)
local notation "rows" => Rows.Receipt G S
local notation "atoms" => PhysicalAffineScalarInputBudget.Term G S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "ρ" => ConditionalAffineSourcePrices.rate (Pt) (S).patch.L

omit [Fintype I] in
/-- Independent scalar roots and all mixed colored legs on the very same
original interior stage. No numerical/smoothness hypothesis on either
removed input, stationary weight, active inverse or finite block is supplied.
The visible multiplier is the exact sum of the authentic changed weights. -/
theorem original {order : ℕ→ℕ→ℕ} (paid : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit) :
    let n := order (j₁) (j₀)
    ∃ a t δ M : ℝ, 0≤a ∧ 0<t ∧ Sheet (T).up t a ∧ 0<δ ∧ 0<M ∧ 0 < min ρ (t/4) ∧
    ∀ (k : (S).Choices) (q : Chi) (b : ℝ) (tag : Site c₀)
    (F' : {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : LinkArray G (Frozen A θ F'.val)) (g : ℝ) (o : Site c₀)
    (l : List (raw G c₀)), l.length≤n →
    |jet (ray G c₀) (ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o) l 0| ≤
      Real.exp (-min ρ (t/4)*(till θ:ℝ)) *
        ∑ z : atoms, ∑ p : Masks l, PhysicalAffineScalarInputBudget.cap S a t δ M n z (lo l p) *
          |jet (ray G c₀) (ManuscriptQLocalRootPrice.weight R d k q b tag F' Y Z g o z) (hi l p) 0| := by
  intro n
  have hPt := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  have hs : 100*(1+radiusB θ)≤(R.alloy.B.a.S.side d.level d.period).val := by
    rw [add_comm 1]; exact R.alloy.B.a.fits.sizeT d.level d.period
  have hc : 1<(c₀).val := by
    change 1 < (R.alloy.B.a.S.side d.level d.period).val
    omega
  have he := ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below
  obtain ⟨σ,K,Λ,hp,hT⟩ := ManuscriptQLocalRootWeights.purchased R d
  have hh := R.alloy.B.support.cap d.cutoff (d.level+1) d.below
  have hsheet : ∃ a t : ℝ, 0≤a ∧ 0<t ∧ Sheet (T).up t a :=
    ⟨_,_,(R.alloy.B.a.params (d.level+1)).paths_pos.le,hh.width,hh.rows⟩
  obtain ⟨a,t,ha,ht,hW⟩ := hsheet
  obtain ⟨δ,M,hδ,hM,hρ,hI⟩ := PhysicalAffineScalarInputBudget.bought G (Pt) (S).patch.L n
  have hS := ManuscriptQLocalScalarSourcePurchase.realized R paid d.cutoff d.level d.period d.below
  refine ⟨a,t,δ,M,ha,ht,hW,hδ,hM,lt_min hρ (by positivity),?_⟩
  intro k q b tag F' Y Z g o l hl
  have inputs := hI S T hPt rfl d.forest θ hS.1 k a t ht ha hW hc hp
  have hfull : Values n (PhysicalAffineScalarUncut.offset T k) := fun i => (hS.2 d.forest k i).1
  have hcut : Values n (shortSource T θ k) := by
    intro i
    have hsrc := (inputs (.inl i)).1
    have h : (fun B : Coarse => shortSource T θ k B i) = fun B => PhysicalAffineScalarUncut.offset T k B i + sourceTail T θ B i := by
      ext B
      have hi := congrFun (PhysicalAffineScalarRetainedSource.full_decomposition T θ k B) i
      simp only [Pi.sub_apply] at hi
      linarith only [hi]
    exact (congrArg (fun f : Coarse → ℝ => ContDiffAt ℝ n f 0) h).mpr ((hfull i).add hsrc)
  have hw₀ := PhysicalAffineScalarWeightRegularity.original T θ k d.forest q b Y g o hp hT ht ha hW hc he n hcut hfull
  have hw₁ := PhysicalAffineScalarWeightRegularity.original T θ k F'.val q b Z g o hp hT ht ha hW hc he n hcut hfull
  have hw (z : atoms) : ContDiffAt ℝ n (ManuscriptQLocalRootPrice.weight R d k q b tag F' Y Z g o z) 0 := by
    rcases z with i|⟨i,j⟩
    · exact (hw₁.1 i).sub (hw₀.1 i)
    · exact (hw₁.2 i j).sub (hw₀.2 i j)
  let cap := PhysicalAffineScalarInputBudget.cap (G:=G) S a t δ M n
  simpa only [one_mul] using ManuscriptQLocalRootPrice.original R d k q b tag F' Y Z g o (ray G c₀) l
    1 (min ρ (t/4)) (till θ) cap (fun z => (inputs z).1.of_le (by exact_mod_cast hl))
    (fun z => (hw z).of_le (by exact_mod_cast hl))
    (fun z s hs => by
      rw [one_mul]
      exact (inputs z).2 s (hs.trans hl))

end YM.Integration.ManuscriptQLocalPaidRootSquare
