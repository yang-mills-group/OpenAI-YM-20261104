import YM.Integration.PhysicalAffineScalarMetric
import YM.Integration.ManuscriptQLocalAffine
import YM.Integration.ManuscriptQLocalSector
import YM.Integration.ActualRunSpring
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Station
import YM.Integration.ManuscriptQLocalStationaryGeometry

/-! The fully uncut Gaussian scalar in the actual selected no-hole term of
the original Run. The true coupled exponent is integrated against the full
curved stationary law on the original active coordinates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalAffineScalar

open Function Filter MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Progress.DirectedRecipe
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section reference
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {path : PathData G}
    {J : ChartRatio G} (κ : Bulk.Kernel S p path J)

/-- Arbitrary tree and selector draws have the same independently prescribed
flat covariance determinant. The nonorthogonal tree transition has unit
absolute Jacobian because both normalized Haar chart products equal one. -/
theorem covariance_det (F F' : Forest S.ratio) (k k' : S.Choices) :
    (κ.covariance F k).det = (κ.covariance F' k').det := by
  obtain ⟨σ,C,Λ,h⟩ := κ.bounds
  obtain ⟨η,hη,hgap⟩ := κ.gap F'
  let e := Work.F05.freeEquiv F F'
  have hx := Work.F05.graph_switch κ.branches h (κ.critical F) (κ.critical F') hη hgap k
  have hd := (Work.F05.hessian_ratio κ.branches h (κ.critical F) (κ.critical F') e hx k).self_of_nhds
  rw [(κ.critical F).1,(κ.critical F').1] at hd
  have ht := (Work.F05.toll_switch (P:=J) e κ.ratio).self_of_nhds
  dsimp only [Prod.fst_zero,Prod.snd_zero] at ht
  rw [Work.F05.switch_zero] at ht
  simp only [Work.F05.toll,Pi.zero_apply,κ.ratio.anchored,Finset.prod_const_one,mul_one] at ht
  have hone : (fderiv ℝ (Work.F05.move e (0:Bid.Dir G c)) 0).det ^ 2 = 1 := by
    rw [←sq_abs,←ht]
    norm_num
  rw [hone,one_mul] at hd
  rw [← κ.convention F' k k']
  change (hessian F k p path 0 0)⁻¹.det = (hessian F' k p path 0 0)⁻¹.det
  rw [Matrix.det_nonsing_inv,Matrix.det_nonsing_inv,hd]
end reference

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "A₀" => noHole Δ
local notation "K" => d.kernel (RunFormalChain.fromRun R)
local notation "Coarse" => Gaussian.Vec (Raw G (R.family.side d.level d.period))
local notation "e" => live (G:=G) A₀ d.forest Θ
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "b" => radiusW R.kit.rider i₁ i₀ * R.alloy.B.a.clock.threshold (d.level+1)

set_option maxHeartbeats 1200000 in
/-- The conditional flat covariance used by the uncut residual-square and
logarithm is exactly the independent kernel prescribed on the actual datum. -/
theorem covariance (k : (Δ).Choices) :
    (PhysicalAffineScalarUncut.gram T Θ k d.forest (0:Coarse))⁻¹ =
      ((K).covariance d.forest k).submatrix e e := by
  rw [PhysicalAffineScalarMetric.uncut]
  exact ManuscriptQLocalAffine.all_keys R d Θ k

theorem positive (k : (Δ).Choices) :
    (PhysicalAffineScalarUncut.gram T Θ k d.forest (0:Coarse)).PosDef := by
  let M := PhysicalAffineScalarUncut.gram T Θ k d.forest (0:Coarse)
  have h : M⁻¹.PosDef := by
    change (PhysicalAffineScalarUncut.gram T Θ k d.forest (0:Coarse))⁻¹.PosDef
    rw [covariance R d k]
    exact ((K).positive d.forest k).submatrix (e).injective
  have hu : IsUnit M.det := IsUnit.mk0 _ (by
    intro hzero
    have hh := h.det_pos
    rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,hzero,_root_.inv_zero] at hh
    exact lt_irrefl _ hh)
  change M.PosDef
  rw [← Matrix.nonsing_inv_nonsing_inv M hu]
  exact h.inv

set_option maxHeartbeats 1200000 in
/-- Positivity through an actual neighborhood follows from the original
Run's true-width path budget and size, together with Gram semidefiniteness. -/
theorem positive_near (k : (Δ).Choices) :
    ∀ᶠ B : Coarse in 𝓝 0, (PhysicalAffineScalarUncut.gram T Θ k d.forest B).PosDef := by
  have hs : Bid.Larger (G:=G) Δ :=
    ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below
  have hp := R.alloy.B.support.cap d.cutoff (d.level+1) d.below
  have hsmooth := FreeResolvent.Affine.knows d.forest k hp.width
      (R.alloy.B.a.params (d.level+1)).paths_pos.le hp.rows hs (T).high 0 FreeResolvent.Affine.all
  let M := PhysicalAffineScalarUncut.gram T Θ k d.forest
  have hc : ContinuousAt M 0 := by
    change ContinuousAt (fun B : Coarse => PhysicalAffineScalarUncut.gram T Θ k d.forest B) 0
    simp_rw [PhysicalAffineScalarMetric.uncut]
    exact (continuous_id.matrix_submatrix e e).continuousAt.comp hsmooth.smooth.continuousAt
  have hd : ContinuousAt (fun B : Coarse => (M B).det) 0 :=
    (Continuous.matrix_det continuous_id).continuousAt.comp hc
  filter_upwards [hd.eventually_ne (positive R d k).det_pos.ne'] with B hB
  let L := PhysicalAffineScalarUncut.columns T Θ k d.forest B
  have hsemi : (M B).PosSemidef := by
    change (L.transpose*L).PosSemidef
    have he : L.conjTranspose=L.transpose := by ext i j; rfl
    exact he ▸ Matrix.posSemidef_conjTranspose_mul_self L
  exact hsemi.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ hB))

private theorem active_det (k : (Δ).Choices) :
    (PhysicalAffineScalarUncut.gram T Θ k d.forest (0:Coarse))⁻¹.det =
      ((K).covariance d.forest k).det := by
  rw [covariance R d k]
  let a := (Native.lineEquiv (G:=G) d.forest Θ).symm
  change (((K).covariance d.forest k).submatrix a a).det = _
  exact Matrix.det_submatrix_equiv_self ..

/-- The original uncut flat chart charge is common to all real tree/tag
draws at fixed physical scale, including its active-coordinate power of
the Haar chart scale. It therefore factors from every marked/quiet sum. -/
theorem outside_common (V : Config G (R.family.side d.level d.period))
    (F' : Forest (Δ).ratio) (k k' : (Δ).Choices) (J : ChartRatio G) :
    Marked.outside T Θ V A₀ P d.forest J (PhysicalAffineScalarUncut.gram T Θ k d.forest 0)⁻¹ =
      Marked.outside T Θ V A₀ P F' J (PhysicalAffineScalarUncut.gram T Θ k' F' 0)⁻¹ := by
  let d' : LocalFormal.Datum R.family Γ := {d with forest:=F'}
  have hd := (active_det R d k).trans ((covariance_det K d.forest F' k k').trans (active_det R d' k').symm)
  let r : Active A₀ Θ d.forest ≃ Active A₀ Θ F' :=
    ((Native.every d.forest Θ).symm.trans (Work.F05.freeEquiv d.forest F')).trans (Native.every F' Θ)
  have hs := congrArg (fun n : ℕ => J.scale^n) (Fintype.card_congr r)
  have he := congrArg (fun n : ℕ => Real.sqrt (2*Real.pi*coupling (P).beta^2)^n)
    (Fintype.card_congr (r.prodCongr (Equiv.refl G.ColorIndex)))
  unfold Marked.outside chartCost
  exact congrArg₂ (fun (a₁ a₂ : ℝ) => a₁*a₂)
    (congrArg (fun a : ℝ => sieve T (P).beta Θ V * prefactor Δ G (P).beta * a) hs)
    (congrArg₂ (fun (a₁ a₂ : ℝ) => a₁*a₂) he (congrArg Real.sqrt hd))

section measured
local notation "V" => fun B : Coarse => represent (decode B)
local notation "g" => coupling (P).beta
local notation "J₀" => R.metals.O

/-- Complete measured signed column and independently specified curved law,
both evaluated on the source placed on the same fine field. -/
def stored (D : Allocation G Δ Θ w) (q : Chi) (k : (Δ).Choices)
    (u : Config G (R.family.side (d.level+1) d.period) → ℂ) (B : Coarse) : ℂ :=
  Marked.amount T Θ P d.forest D q J₀ b u A₀ k (V B)

def gaussian (D : Allocation G Δ Θ w) (q : Chi) (k : (Δ).Choices)
    (u : Config G (R.family.side (d.level+1) d.period) → ℂ) (B : Coarse) : ℂ :=
  Marked.outside T Θ (V B) A₀ P d.forest J₀ (PhysicalAffineScalarUncut.gram T Θ k d.forest 0)⁻¹ •
    ∫ Y, (∫ z,
      let a := PhysicalAffineScalarUncut.center T Θ k d.forest B + g • z
      let y := tape a
      let U := physical A₀ d.forest (V B) Y y
      let weight := reserve q J₀ b y * doors q b y * D.bill A₀ k U (V B) *
        (Δ).likelihood U k * Real.exp (PhysicalAffineScalarUncut.scalar T Θ k d.forest g B -
          (P).beta * (Rows.fee T Θ (V B) k A₀ U - PhysicalAffineScalarUncut.action T Θ k d.forest B a))
      weight • Marked.recut P (till Θ) u U
      ∂Gaussian.cloud (PhysicalAffineScalarUncut.gram T Θ k d.forest B)⁻¹) ∂piHaar G (Frozen A₀ Θ d.forest)

/-- The original charged nonlinear remainder with the full affine polynomial
removed on the very same material fine field. -/
def interaction (D : Allocation G Δ Θ w) (q : Chi) (k : (Δ).Choices)
    (u : Config G (R.family.side (d.level+1) d.period) → ℂ) (B : Coarse) : ℂ :=
  ∫ Y, (∫ z,
    let a := PhysicalAffineScalarUncut.center T Θ k d.forest B + g • z
    let y := tape a
    let U := physical A₀ d.forest (V B) Y y
    (reserve q J₀ b y * doors q b y * D.bill A₀ k U (V B) * (Δ).likelihood U k *
      Real.exp (-((P).beta * (Rows.fee T Θ (V B) k A₀ U -
        PhysicalAffineScalarUncut.action T Θ k d.forest B a)))) • Marked.recut P (till Θ) u U
    ∂Gaussian.cloud (PhysicalAffineScalarUncut.gram T Θ k d.forest B)⁻¹) ∂piHaar G (Frozen A₀ Θ d.forest)

private theorem universes {J : Type*} (L U : Fintype J) : @Finset.univ J L=@Finset.univ J U :=
  Finset.ext fun i => ⟨fun _ => @Finset.mem_univ J U i,fun _ => @Finset.mem_univ J L i⟩

/-- One scalar factor for each original translation. The common flat
outside and all field-sensitive local powers have their physical signs. -/
theorem roots (D : Allocation G Δ Θ w) (q : Chi) (k : (Δ).Choices)
    (u : Config G (R.family.side (d.level+1) d.period) → ℂ)
    (B : Coarse) (hB : (PhysicalAffineScalarUncut.gram T Θ k d.forest B).PosDef) :
    gaussian R d D q k u B =
      (Marked.outside T Θ (V B) A₀ P d.forest J₀ (PhysicalAffineScalarUncut.gram T Θ k d.forest 0)⁻¹ *
        ∏ o : Site (R.family.side d.level d.period), Real.exp
          (PhysicalAffineScalarUncut.scalarAt T Θ k d.forest g o B)) • interaction R d D q k u B := by
  let E := PhysicalAffineScalarUncut.scalar T Θ k d.forest g B
  have h (a z : ℝ) (v : ℂ) : (a*Real.exp (E-z)) • v =
      Real.exp E • ((a*Real.exp (-z)) • v) := by
    rw [sub_eq_add_neg,Real.exp_add,smul_smul]
    congr 1
    ring
  let O := Marked.outside T Θ (V B) A₀ P d.forest J₀ (PhysicalAffineScalarUncut.gram T Θ k d.forest 0)⁻¹
  calc gaussian R d D q k u B = O • (Real.exp E • interaction R d D q k u B) := by
         unfold gaussian interaction
         apply congrArg (fun value : ℂ => O • value)
         simp_rw [← integral_smul]
         apply integral_congr_ae
         filter_upwards with Y
         apply integral_congr_ae
         filter_upwards with z
         exact h _ _ _
       _ = (O*Real.exp E) • interaction R d D q k u B := smul_smul ..
       _ = _ := by
         apply congrArg (fun r : ℝ => (O*r) • interaction R d D q k u B)
         dsimp only [E]
         rw [PhysicalAffineScalarUncut.scalar_sum T Θ k d.forest g B (positive R d k) hB,Real.exp_sum]
         apply Finset.prod_congr (universes _ _)
         intro i _
         rfl

set_option maxHeartbeats 1600000 in
/-- Actual measure identity for every measurable bounded fine source,
including all signed columns of the primary marked sector. -/
theorem column_at (D : Allocation G Δ Θ w) (q : Chi) (k : (Δ).Choices)
    (B : Coarse) (hB : (PhysicalAffineScalarUncut.gram T Θ k d.forest B).PosDef)
    (u : Config G (R.family.side (d.level+1) d.period) → ℂ) (hu : Envelope u) :
    stored R d D q k u B = gaussian R d D q k u B := by
  have license := ManuscriptQLocalSector.bought R d D q
  have previous := (license.fixedTerm hu A₀ k (V B)).result
  obtain ⟨σ,n,Λ,δ,l,hP⟩ := license.lawful
  obtain ⟨Pt,hT⟩ := license.funds
  have permitted : Marked.Permission T Θ (V B) k A₀ P (shots Δ Θ) d.forest D q J₀ b
      (PhysicalAffineScalarUncut.gram T Θ k d.forest B)⁻¹ (fun _ => PhysicalAffineScalarUncut.center T Θ k d.forest B) u := by
    apply Marked.fixed T Θ (V B) k A₀ P (shots Δ Θ) d.forest D q J₀ b hP hT license.fitted _ hu
    intro hf
    have old := license.permits A₀ k (V B) hf
    exact ⟨hB.inv,old.bpos,measurable_const,old.core,old.trueChart,old.doorPos,old.scalePaid⟩
  rw [stored,gaussian,Marked.amount,← previous,permitted.result,Marked.afterChange]
  simp_rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with Y
  apply integral_congr_ae
  filter_upwards with z
  simp only [Marked.ink,smul_smul]
  exact congrArg₂ (fun (r : ℝ) (value : ℂ) => r • value)
    (PhysicalAffineScalarUncut.marked_backdrop T Θ k d.forest
      (R.alloy.B.support.cap d.cutoff (d.level+1) d.below) P license.beta D q J₀ b Y B (positive R d k) hB z) rfl

variable [Fintype I] {J : Request I} {A : NumericSchedule R.family J}
    (H : AnalyticInput J A d) (x : TestSpace J.tests)

/-- The genuine stored marked/quiet numerators, with the same field and
source on both representations, agree in a neighborhood of the origin. -/
theorem original (D : Allocation G Δ Θ w) (q : Chi) (k : (Δ).Choices)
    (s : Γ.Mode) :
    (fun B => stored R d D q k (Actual.atMark s (ManuscriptQLocalActualLog.source R d H x)) B) =ᶠ[𝓝 0]
      fun B => gaussian R d D q k (Actual.atMark s (ManuscriptQLocalActualLog.source R d H x)) B :=
  (positive_near R d k).mono fun B hB =>
    column_at R d D q k B hB _ ((ManuscriptQLocalActualLog.floor R d H x).safe s)

/-- Arbitrarily many independent field/source parameters, with one genuine
tree changed at the specified physical block, and the identical signed
input in both experiments. The center, frozen field and Gaussian law use
their own corresponding actual tree indices. -/
theorem one_tree_jet (D : Allocation G Δ Θ w) (q : Chi) (k : (Δ).Choices)
    (tag : Site (R.family.side d.level d.period))
    (F' : {F : Forest (Δ).ratio // FreeResolvent.Affine.changed Δ d.forest F tag})
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (t : Z) (field : Z → Coarse) (hc : ContinuousAt field t) (h0 : field t=0)
    (tests : Z → TestSpace J.tests) (s : Γ.Mode) (j : ℕ) (v : Fin j → Z) :
    let d' : LocalFormal.Datum R.family Γ := {d with forest:=F'.val}
    let source := fun z : Z => Actual.atMark s (ManuscriptQLocalActualLog.source R d H (tests z))
    iteratedFDeriv ℝ j (fun z : Z => stored R d' D q k (source z) (field z) -
      stored R d D q k (source z) (field z)) t v =
      iteratedFDeriv ℝ j (fun z : Z => gaussian R d' D q k (source z) (field z) -
        gaussian R d D q k (source z) (field z)) t v := by
  intro d' source
  have ht : Tendsto field (𝓝 t) (𝓝 0) := h0 ▸ hc.tendsto
  have hs (z : Z) : Envelope (source z) := (ManuscriptQLocalActualLog.floor R d H (tests z)).safe s
  have he : (fun z => stored R d' D q k (source z) (field z) - stored R d D q k (source z) (field z)) =ᶠ[𝓝 t]
      fun z => gaussian R d' D q k (source z) (field z) - gaussian R d D q k (source z) (field z) := by
    filter_upwards [ht.eventually (positive_near R d' k),ht.eventually (positive_near R d k)] with z h' h
    rw [column_at R d' D q k (field z) h' (source z) (hs z),column_at R d D q k (field z) h (source z) (hs z)]
  rw [(he.iteratedFDeriv (𝕜:=ℝ) j).self_of_nhds]
end measured
end YM.Integration.ManuscriptQLocalAffineScalar
end
