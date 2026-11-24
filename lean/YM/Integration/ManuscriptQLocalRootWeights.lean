import YM.Integration.PhysicalAffineScalarGaussianWeights
import YM.Integration.ManuscriptQLocalAffineScalar

/-! A single charged original no-hole Run. The true metric cone for the cut
and the independent full action is purchased from its native flat gap. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalRootWeights
open Function Filter Matrix Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree Pressure
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Pressure.Testing Pressure.Stores
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato Progress.DirectedRecipe PhysicalAffineScalarCutWeights
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "W" => shots S θ
local notation "Coarse" => Gaussian.Vec (Raw G (R.family.side d.level d.period))
local notation "V" => fun B : Coarse => represent (decode B)
local notation "c₀" => R.family.side d.level d.period
local notation "f₀" => R.family.side (d.level+1) d.period
local notation "rows" => Rows.Receipt G S

omit [Fintype I] in
theorem purchased : ∃ σ K Λ : ℝ, (S).patch.Branches (S).kernel G ∧ (T).up.Bounds (T).high σ K Λ := by
  have hP := Pressure.Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  obtain ⟨_,_,hu,_⟩ := hP.feeds
  rw [←hP.high] at hu
  exact ⟨_,_,_,Push.SectorMeasure.funds_branch hP,hu⟩

/-- A true cut or full Gram on any one of this stage's actual trees is
strictly positive in a genuine neighbourhood of the common zero field. -/
private theorem positive_of_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (M : Matrix β β ℝ)
    (hsemi : (M.submatrix e e).PosSemidef) (hdet : M.det ≠ 0) :
    (M.submatrix e e).PosDef := by
  apply hsemi.posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_submatrix_equiv_self e M]
  exact IsUnit.mk0 _ hdet

omit [Fintype I] in
theorem positive (k : (S).Choices) (F : Forest (S).ratio) :
    ∀ᶠ B : Coarse in 𝓝 0, (Rows.gram T θ (V B) k W A F).PosDef ∧ (PhysicalAffineScalarUncut.gram T θ k F B).PosDef := by
  let d' : LocalFormal.Datum R.family Γ := {d with forest:=F}
  let e : Rows.In (G:=G) θ A F ≃ Precision.Key F G := (Native.lineEquiv F θ).symm
  let M := primary S F k (T).high (T).up (shorter (till θ))
  obtain ⟨σ,E,Λ,hb,hT⟩ := purchased R d
  have hg : ∀ᶠ B : Coarse in 𝓝 0, Rows.gram T θ (V B) k W A F=(M B).submatrix e e :=
    affine_near A F θ T k hb hT
  let J := ActualRunSpring.selected R d.cutoff d.period d.level d.below
  have hl : Bid.Larger (G:=G) S := (J.spring.H.houses J.point).laws.data.room.larger
  have hp := R.alloy.B.support.cap d.cutoff (d.level+1) d.below
  have hk := FreeResolvent.Affine.knows F k hp.width (R.alloy.B.a.params (d.level+1)).paths_pos.le hp.rows hl (T).high 0 (shorter (till θ))
  have hd : ContinuousAt (fun B : Coarse => (M B).det) 0 := (Continuous.matrix_det continuous_id).continuousAt.comp hk.smooth.continuousAt
  have hn : (M 0).det ≠ 0 := (hk.gap.unit_det (headGap_pos ..)).ne_zero
  filter_upwards [hg,hd.eventually_ne hn,ManuscriptQLocalAffineScalar.positive_near R d' k] with B hM hB hu
  refine ⟨?_,hu⟩
  let L := Rows.move T θ (V B) k W A F
  have hsemi : (Rows.gram T θ (V B) k W A F).PosSemidef := by
    change (L.transpose*L).PosSemidef
    have he : L.conjTranspose=L.transpose := by ext i j; rfl
    exact he ▸ Matrix.posSemidef_conjTranspose_mul_self L
  rw [hM] at hsemi ⊢
  exact positive_of_reindex e (M B) hsemi hB

variable (k : (R.family.path.levels.clock.op d.level d.period).Choices) (q : Chi) (b : ℝ) (tag : Site (R.family.side d.level d.period))
    (F' : {U : Forest (R.family.path.levels.clock.op d.level d.period).ratio // changed (R.family.path.levels.clock.op d.level d.period) d.forest U tag})
    (Y : LinkArray G (Frozen (noHole (R.family.path.levels.clock.op d.level d.period)) (R.alloy.B.a.clock.hatBeta d.level) d.forest)) (Y' : LinkArray G (Frozen (noHole (R.family.path.levels.clock.op d.level d.period)) (R.alloy.B.a.clock.hatBeta d.level) F'.val)) (g : ℝ) (o : Site (R.family.side d.level d.period))

omit [Fintype I] in
/-- Full one-tag root error. The logarithmic term is independently paired
on each actual tree. The two genuine removed raw coefficients are shared
across draws, and the entire tree change is on ordinary computed weights. -/
theorem original :
    (fun B : Coarse => (PhysicalAffineScalarJets.actualRoot T θ k A F'.val q b Y' g o B -
      PhysicalAffineScalarJets.actualRoot T θ k A d.forest q b Y g o B) -
      (PhysicalAffineScalarUncut.scalarAt T θ k F'.val g o B - PhysicalAffineScalarUncut.scalarAt T θ k d.forest g o B)) =ᶠ[𝓝 0]
    fun B : Coarse => (PhysicalAffineScalarCutResidual.logGap T θ k F'.val o B - PhysicalAffineScalarCutResidual.logGap T θ k d.forest o B) +
      ((∑ z : rows, sourceTail T θ B z*(rowWeight T θ k F'.val q b Y' g o z B - rowWeight T θ k d.forest q b Y g o z B)) +
       ∑ z : rows, ∑ j : Raw G f₀, columnTail T θ k B z j * (columnWeight T θ k F'.val q b Y' g o z j B -
         columnWeight T θ k d.forest q b Y g o z j B)) := by
  obtain ⟨σ,E,Λ,h,hT⟩ := purchased R d
  have hr := PhysicalAffineScalarCutWeights.one_tree T θ k d.forest q b tag F' Y Y' g o h hT (fun Z _ => positive R d k Z)
  filter_upwards [hr] with B hB
  exact (PhysicalAffineScalarCutResidual.one_tree T θ k d.forest q b tag F' Y Y' g o B).trans
    (congrArg (fun z : ℝ => (PhysicalAffineScalarCutResidual.logGap T θ k F'.val o B -
      PhysicalAffineScalarCutResidual.logGap T θ k d.forest o B) + z) hB)

omit [Fintype I] in
theorem mixed (j : ℕ) (v : Fin j → Coarse) :
    iteratedFDeriv ℝ j (fun B : Coarse => (PhysicalAffineScalarJets.actualRoot T θ k A F'.val q b Y' g o B -
      PhysicalAffineScalarJets.actualRoot T θ k A d.forest q b Y g o B) -
      (PhysicalAffineScalarUncut.scalarAt T θ k F'.val g o B - PhysicalAffineScalarUncut.scalarAt T θ k d.forest g o B)) 0 v =
    iteratedFDeriv ℝ j (fun B : Coarse =>
      (PhysicalAffineScalarCutResidual.logGap T θ k F'.val o B - PhysicalAffineScalarCutResidual.logGap T θ k d.forest o B) +
      ((∑ z : rows, sourceTail T θ B z*(rowWeight T θ k F'.val q b Y' g o z B - rowWeight T θ k d.forest q b Y g o z B)) +
       ∑ z : rows, ∑ a : Raw G f₀, columnTail T θ k B z a*(columnWeight T θ k F'.val q b Y' g o z a B -
         columnWeight T θ k d.forest q b Y g o z a B))) 0 v := by
  rw [((original R d k q b tag F' Y Y' g o).iteratedFDeriv (𝕜:=ℝ) j).self_of_nhds]

end YM.Integration.ManuscriptQLocalRootWeights
