import YM.Integration.ManuscriptQLocalAffineScalar
import YM.Integration.PhysicalAffineScalarGaussianWeights
import YM.Integration.PhysicalAffineScalarJets

/-! Charged and complementary terms of the original physical conditional, at arbitrary jet order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMeasuredConditional.Cut
open Function Filter Matrix Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree Pressure
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Pressure.Testing Pressure.Stores
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato Progress.DirectedRecipe PhysicalAffineScalarCutWeights
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "W" => shots S θ
local notation "Coarse" => Gaussian.Vec (Raw G (R.family.side d.level d.period))
local notation "V" => fun B : Coarse => represent (decode B)
local notation "c₀" => R.family.side d.level d.period
local notation "f₀" => R.family.side (d.level+1) d.period
local notation "rows" => Rows.Receipt G S

theorem purchased : ∃ σ K Λ : ℝ, (S).patch.Branches (S).kernel G ∧ (T).up.Bounds (T).high σ K Λ := by
  have hP := Pressure.Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  obtain ⟨_,_,hu,_⟩ := hP.feeds
  rw [←hP.high] at hu
  exact ⟨_,_,_,Push.SectorMeasure.funds_branch hP,hu⟩

/-- A true cut or full Gram on any one of this stage's actual trees is
strictly positive in a genuine neighbourhood of the common zero field. -/
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
  apply hsemi.posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [hM]
  have hdet := Matrix.det_submatrix_equiv_self e (M B)
  exact hdet.symm ▸ IsUnit.mk0 _ hB

end YM.Integration.ManuscriptQLocalMeasuredConditional.Cut

namespace YM.Integration.ManuscriptQLocalMeasuredConditional

open Function Filter MeasureTheory Matrix Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree Pressure
open Next.SectorChange Gaussian Pressure.Testing Pressure.Stores
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "A₀" => noHole Δ
local notation "J₀" => R.metals.O
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "b" => radiusW R.kit.rider i₁ i₀ * R.alloy.B.a.clock.threshold (d.level+1)
local notation "Coarse" => Gaussian.Vec (Raw G (R.family.side d.level d.period))
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "g" => coupling (P).beta

variable (D : Allocation G (R.family.path.levels.clock.op d.level d.period) (R.alloy.B.a.clock.hatBeta d.level)
  (R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))) (q : Chi)

local notation "W" => shots Δ Θ
local notation "F" => d.forest
local notation "Q" => fun (k : (Δ).Choices) (B : Coarse) => Rows.gram T Θ (V B) k W A₀ F
local notation "m" => fun (k : (Δ).Choices) (B : Coarse) (Y : LinkArray G (Frozen A₀ Θ F)) =>
  PhysicalAffineScalarComparison.stationary T Θ (V B) k W A₀ F q b Y
local notation "Y₀" => (1 : LinkArray G (Frozen A₀ Θ F))


def retained (u : Fine → ℂ) (B : Coarse) : ℂ :=
  ∑ k : (Δ).Choices, ManuscriptQLocalAffineScalar.stored R d D q k u B

def holes (u : Fine → ℂ) (B : Coarse) : ℂ :=
  ∑ A ∈ Finset.univ.erase A₀, ∑ k : (Δ).Choices, Marked.amount T Θ P d.forest D q J₀ b u A k (V B)

private theorem frozen (Y : LinkArray G (Frozen A₀ Θ F)) : Y=Y₀ := by
  funext i; exact ((Native.every F Θ i.val).property i.property).elim

def common (k : (Δ).Choices) (B : Coarse) := Marked.outside T Θ (V B) A₀ P F J₀ (Q k 0)⁻¹

def interaction (k : (Δ).Choices) (u : Fine→ ℂ) (B : Coarse) : ℂ :=
  ∫ Y : LinkArray G (Frozen A₀ Θ F), (∫ z : Prices G (Active A₀ Θ F),
    let a : Prices G (Active A₀ Θ F) := fun edge => m k B Y₀ edge + g * z edge
    let y : LogArray G (Active A₀ Θ F) := tape a
    let U := physical A₀ F (V B) Y y
    (reserve q J₀ b y*doors q b y*D.bill A₀ k U (V B)*(Δ).likelihood U k*
      Real.exp (-(P).beta*averaged (Rows.residual T Θ (V B) k W A₀ F q b Y U a))) •
      Marked.recut P (till Θ) u U ∂Gaussian.cloud (Q k B)⁻¹) ∂piHaar G (Frozen A₀ Θ F)

def row (k : (Δ).Choices) (u : Fine→ ℂ) (B : Coarse) :=
  (∏ o : Site (R.family.side d.level d.period), Real.exp (PhysicalAffineScalarJets.actualRoot T Θ k A₀ F q b Y₀ g o B)) •
    interaction R d D q k u B

private theorem combine_roots {ι : Type} [Fintype ι] (base logPrice shift value residual : ℝ)
    (p : ι → ℝ) (total : logPrice + shift = ∑ i, p i) :
    base * Real.exp logPrice * (value * Real.exp (residual + shift)) =
      base * ((∏ i, Real.exp (p i)) * (value * Real.exp residual)) := by
  rw [←Real.exp_sum, ←total, Real.exp_add, Real.exp_add]
  ring

private theorem backdrop (k : (Δ).Choices) (B : Coarse) (hB : (Q k B).PosDef)
    (z : Prices G (Active A₀ Θ F)) :
    let a : Prices G (Active A₀ Θ F) := fun edge => m k B Y₀ edge + g * z edge
    let y : LogArray G (Active A₀ Θ F) := tape a
    let U := physical A₀ F (V B) Y₀ y
    Marked.outside T Θ (V B) A₀ P F J₀ (Q k B)⁻¹ * Marked.backdrop T Θ (V B) k A₀ P W F D q J₀ b (Q k B)⁻¹ (fun _ => m k B Y₀) Y₀ z =
      common R d k B * ((∏ o : Site (R.family.side d.level d.period), Real.exp (PhysicalAffineScalarJets.actualRoot T Θ k A₀ F q b Y₀ g o B)) *
      (reserve q J₀ b y*doors q b y*D.bill A₀ k U (V B)*(Δ).likelihood U k*
        Real.exp (-(P).beta*averaged (Rows.residual T Θ (V B) k W A₀ F q b Y₀ U a)))) := by
  intro a y U
  let C := (Q k B)⁻¹
  let C₀ := (Q k 0)⁻¹
  let L := Real.log (chartCost C g/chartCost C₀ g)
  let J := Rows.adjustment T Θ (V B) k W A₀ F q b Y₀ C (m k B Y₀) g z
  let X := -(P).beta*averaged (Rows.residual T Θ (V B) k W A₀ F q b Y₀ U a)
  let t := reserve q J₀ b y*doors q b y*D.bill A₀ k U (V B)*(Δ).likelihood U k
  have hg := coupling_pos (ManuscriptQLocalSector.bought R d D q).beta
  have h₀ := (Cut.positive R d k F).self_of_nhds.1
  have hc₀ : 0<chartCost C₀ g := chartCost_pos C₀ h₀.inv hg
  have hO : Marked.outside T Θ (V B) A₀ P F J₀ C = common R d k B*Real.exp L := by
    unfold common Marked.outside; rw [show Real.exp L=chartCost C g/chartCost C₀ g from Real.exp_log (div_pos (chartCost_pos C hB.inv hg) hc₀)]
    change _ * chartCost C g = _ * chartCost C₀ g * (chartCost C g/chartCost C₀ g); field_simp [hc₀.ne']
  have e := PhysicalAffineScalarJets.sum_actual T Θ k A₀ F q b Y₀ g hg B h₀ hB z
  change L+J=∑ o,PhysicalAffineScalarJets.actualRoot T Θ k A₀ F q b Y₀ g o B at e
  change Marked.outside T Θ (V B) A₀ P F J₀ C*(t*Real.exp (X+J))=common R d k B*((∏ o,Real.exp _)*(t*Real.exp X))
  rw [hO]
  exact combine_roots _ L J t X _ e

private theorem displacement {ι : Type} [Fintype ι] (a z : Prices G ι) (g₀ : ℝ) :
    displaced a g₀ z = tape (fun i => a i + g₀ * z i) := by rfl

private theorem integrate_weight {A : Type*} [MeasurableSpace A] (μ : Measure A) (r : ℝ)
    (f₁ f₂ : A → ℂ) (eq : ∀ z, f₁ z = r • f₂ z) :
    (∫ z, f₁ z ∂μ) = r • ∫ z, f₂ z ∂μ :=
  (integral_congr_ae (Filter.Eventually.of_forall eq)).trans (integral_smul r f₂)

/-- The cut and uncut scalar and both interactions come from the same
licensed original measured column, for every bounded measurable signed source. -/
theorem column (k : (Δ).Choices) (B : Coarse) (hB : (Q k B).PosDef) (u : Fine→ ℂ) (hu : Envelope u) :
    ManuscriptQLocalAffineScalar.stored R d D q k u B = common R d k B • row R d D q k u B := by
  let license := ManuscriptQLocalSector.bought R d D q
  have before := (license.fixedTerm hu A₀ k (V B)).result
  obtain ⟨σ,n,Λ,δ,l,hP⟩ := license.lawful
  obtain ⟨Pt,hT⟩ := license.funds
  have permit : Marked.Permission T Θ (V B) k A₀ P W F D q J₀ b (Q k B)⁻¹ (fun _ => m k B Y₀) u := by
    apply Marked.fixed T Θ (V B) k A₀ P W F D q J₀ b hP hT license.fitted _ hu
    intro hf; have old := license.permits A₀ k (V B) hf
    exact ⟨hB.inv,old.bpos,measurable_const,old.core,old.trueChart,old.doorPos,old.scalePaid⟩
  rw [ManuscriptQLocalAffineScalar.stored,Marked.amount,←before,permit.result,Marked.afterChange,row,interaction]
  simp_rw [←integral_smul]; apply integral_congr_ae; filter_upwards with Y
  rw [smul_smul]
  apply integrate_weight
  intro z
  rw [frozen R d Y]; simp only [Marked.ink,smul_smul]
  refine congrArg₂ (fun (r : ℝ) (value : ℂ) => r • value) ?_ ?_
  · simpa only [mul_assoc] using backdrop R d D q k B hB z
  · apply congrArg (Marked.recut P (till Θ) u)
    apply congrArg (physical A₀ F (V B) Y₀)
    rw [displacement]
    rfl

theorem same_flat (k k' : (Δ).Choices) (B : Coarse) : common R d k B=common R d k' B := by
  obtain ⟨_,_,_,hp,hT⟩ := Cut.purchased R d
  have hV : V (0:Coarse) = (1:Config G (R.family.side d.level d.period)) := by
    change represent (decode (0 : Coarse)) = _
    exact (congrArg represent ((plain G (R.family.side d.level d.period) 1).map_zero)).trans (link_one ..)
  have h := PhysicalAffineScalarAperture.flat_chart T Θ k F F k' hp hT g
  dsimp only [common, Marked.outside]
  dsimp only at hV
  simp only [hV]
  exact congrArg (fun chart : ℝ => _ * chart) h

/-- The only factor taken out of the selector sum is the true positive
flat chart factor. Every field- and selector-dependent root remains in the sum. -/
theorem charged (k₀ : (Δ).Choices) (B : Coarse) (hB : ∀ k,(Q k B).PosDef) (u : Fine→ ℂ) (hu : Envelope u) :
    retained R d D q u B = common R d k₀ B • ∑ k : (Δ).Choices,row R d D q k u B := by
  unfold retained; rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => (column R d D q k B (hB k) u hu).trans (by rw [same_flat R d k k₀ B])

/-- Exact original marked partition, retaining every unremoved sector in
its true selected physical chart. -/
theorem full (k₀ : (Δ).Choices) (B : Coarse) (hB : ∀ k,(Q k B).PosDef) (u : Fine→ ℂ) (hu : Envelope u) :
    Marked.paidSum T Θ P F D q J₀ b u (V B) = common R d k₀ B • (∑ k : (Δ).Choices,row R d D q k u B) +
      holes R d D q u B := by
  rw [←charged R d D q k₀ B hB u hu]
  exact (Finset.add_sum_erase (s:=Finset.univ)
    (fun A : Stores Δ => ∑ k : (Δ).Choices, Marked.amount T Θ P F D q J₀ b u A k (V B)) (Finset.mem_univ A₀)).symm

variable [Fintype I] {J : Request I} {A : NumericSchedule R.family J} (H : AnalyticInput J A d) (x : TestSpace J.tests)
local notation "Π" => ManuscriptQLocalActualLog.source R d H x
local notation "u" => fun s : Γ.Mode => Actual.atMark s Π

def measured (k₀ : (Δ).Choices) (s : Γ.Mode) (B : Coarse) : ℂ :=
  (common R d k₀ B • (∑ k : (Δ).Choices,row R d D q k (u s) B) + holes R d D q (u s) B) /
  (common R d k₀ B • (∑ k : (Δ).Choices,row R d D q k (u Γ.quiet) B) + holes R d D q (u Γ.quiet) B)

theorem conditional_at (k₀ : (Δ).Choices) (s : Γ.Mode) (B : Coarse) (hB : ∀ k,(Q k B).PosDef) :
    (Actual.Push Δ (P).beta Π (V B)).part s/((P₀).eval (V B):ℂ)=measured R d D q H x k₀ s B := by
  rw [ManuscriptQLocalSector.numerator R d H x D q (V B) s,←ManuscriptQLocalSector.denominator R d H x D q (V B),measured]
  have h := ManuscriptQLocalActualLog.floor R d H x
  rw [full R d D q k₀ B hB (u s) (h.safe s),full R d D q k₀ B hB (u Γ.quiet) (h.safe Γ.quiet)]

theorem conditional (k₀ : (Δ).Choices) (s : Γ.Mode) :
    (fun B : Coarse => (Actual.Push Δ (P).beta Π (V B)).part s / ((P₀).eval (V B):ℂ)) =ᶠ[𝓝 0]
      measured R d D q H x k₀ s := by
  have Hp := Filter.eventually_all.mpr (fun k : (Δ).Choices => Cut.positive R d k F)
  filter_upwards [Hp] with B hB; exact conditional_at R d D q H x k₀ s B (fun k => (hB k).1)

theorem conditional_jet (k₀ : (Δ).Choices) (s : Γ.Mode) (j : ℕ) (v : Fin j→ Coarse) :
    iteratedFDeriv ℝ j (fun B : Coarse => (Actual.Push Δ (P).beta Π (V B)).part s/((P₀).eval (V B):ℂ)) 0 v =
      iteratedFDeriv ℝ j (measured R d D q H x k₀ s) 0 v := by
  rw [((conditional R d D q H x k₀ s).iteratedFDeriv ℝ j).self_of_nhds]

/-- Independent physical coarse fields and varying external test data can
be read on the same auxiliary chart; the positivity neighbourhood is
purchased independently of every insertion and its mode. -/
theorem joint_jet (k₀ : (Δ).Choices) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (t : Z) (field : Z→ Coarse) (hc : ContinuousAt field t) (h₀ : field t=0)
    (tests : Z→ TestSpace J.tests) (mode : Γ.Mode) (j : ℕ) (v : Fin j→ Z) :
    let source := fun z => ManuscriptQLocalActualLog.source R d H (tests z)
    iteratedFDeriv ℝ j (fun z => (Actual.Push Δ (P).beta (source z) (V (field z))).part mode/((P₀).eval (V (field z)):ℂ)) t v =
      iteratedFDeriv ℝ j (fun z => measured R d D q H (tests z) k₀ mode (field z)) t v := by
  intro source
  have hfield : Filter.Tendsto field (𝓝 t) (𝓝 0) := h₀ ▸ hc.tendsto
  have hp := Filter.eventually_all.mpr (fun k : (Δ).Choices => Cut.positive R d k F)
  have eq : (fun z => (Actual.Push Δ (P).beta (source z) (V (field z))).part mode/((P₀).eval (V (field z)):ℂ)) =ᶠ[𝓝 t]
      fun z => measured R d D q H (tests z) k₀ mode (field z) := by
    filter_upwards [hfield.eventually hp] with z hz
    exact conditional_at R d D q H (tests z) k₀ mode (field z) (fun k => (hz k).1)
  rw [(eq.iteratedFDeriv ℝ j).self_of_nhds]

end YM.Integration.ManuscriptQLocalMeasuredConditional
end
