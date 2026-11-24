import YM.Integration.ManuscriptQLocalAffineScalar
import YM.Integration.PhysicalForestAction

/-! The genuine source-carrying sector on the fixed independent Gaussian.
Both reference parameters are selected by the actual Run formal chain.
The coarse background and frozen exterior are retained. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatReference
open Function Filter MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Progress.DirectedRecipe
open scoped Matrix.Norms.Frobenius
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type} [DecidableEq I] {Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "K" => d.kernel (RunFormalChain.fromRun R)
local notation "g" => Next.SectorChange.coupling (P).beta
local notation "J₀" => R.metals.O
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "b" => radiusW R.kit.rider i₁ i₀ * R.alloy.B.a.clock.threshold (d.level+1)
local notation "Coarse" => fieldDir G (R.family.side d.level d.period) 1

def covariance (A:Stores Δ)(k:(Δ).Choices):Gaussian.Table (In (G:=G) Θ A d.forest):=
  ((K).covariance d.forest k).submatrix (live A d.forest Θ) (live A d.forest Θ)

def shift (A:Stores Δ)(x:Coarse):Prices G (Active A Θ d.forest):=
  fun i=>g*((fderiv ℝ ((K).b d.forest) 0 x) i.1.1) i.2

/-- The chosen moving argument is the actual restriction of Bulk.translated
at the held coarse direction, including its nonzero deterministic position. -/
theorem plated (A:Stores Δ)(x:Coarse)(z:Precision.Key d.forest G→ℝ)(i:In (G:=G) Θ A d.forest):
    (shift R d A x+g • (z ∘ live A d.forest Θ)) i=
      g*((Bulk.translated K d.forest x z).2.2 i.1.1) i.2:=by
  rw [Bulk.footing]
  change g*(((fderiv ℝ ((K).b d.forest) 0 x) i.1.1) i.2)+g*(z (live A d.forest Θ i))=
    g*((((fderiv ℝ ((K).b d.forest) 0 x) i.1.1) i.2)+z (live A d.forest Θ i))
  ring

theorem positive (A:Stores Δ)(k:(Δ).Choices):(covariance R d A k).PosDef:=
  ((K).positive d.forest k).submatrix (live A d.forest Θ).injective

/-- Each stored conditional law is the restriction of the one full
independently prescribed Gaussian, on all genuine participating keys. -/
theorem projected (A:Stores Δ)(k:(Δ).Choices):
    MeasurePreserving (fun z:Precision.Key d.forest G→ℝ=>z ∘ live A d.forest Θ)
      (Gaussian.cloud ((K).covariance d.forest k)) (Gaussian.cloud (covariance R d A k)):=
  AnalyticBridge.Sharp.Projection.cloud_projection ((K).positive d.forest k) (live A d.forest Θ)

def chart (D:Allocation G Δ Θ w)(q:Chi)(A:Stores Δ)(k:(Δ).Choices)(V:Config G (R.family.side d.level d.period))
    (x:Coarse)(u:Config G (R.family.side (d.level+1) d.period)→ℂ):ℂ:=
  Marked.afterChange T Θ V k A P (shots Δ Θ) d.forest D q J₀ b (covariance R d A k)
    (fun _=>shift R d A x) u

theorem permit (D:Allocation G Δ Θ w)(q:Chi)(A:Stores Δ)(k:(Δ).Choices)
    (V:Config G (R.family.side d.level d.period))(x:Coarse)
    (u:Config G (R.family.side (d.level+1) d.period)→ℂ)(hu:Envelope u):
    Marked.Permission T Θ V k A P (shots Δ Θ) d.forest D q J₀ b (covariance R d A k)
      (fun _=>shift R d A x) u:=by
  have license:=ManuscriptQLocalSector.bought R d D q
  obtain ⟨σ,n,Λ,δ,l,hP⟩:=license.lawful
  obtain ⟨Pt,hT⟩:=license.funds
  apply Marked.fixed T Θ V k A P (shots Δ Θ) d.forest D q J₀ b hP hT license.fitted _ hu
  intro hf
  have old:=license.permits A k V hf
  exact ⟨positive R d A k,old.bpos,measurable_const,old.core,old.trueChart,old.doorPos,old.scalePaid⟩

/-- This equality is pointwise in the real coarse compact field. Any
incoming bounded measured numerator may use the same sector and chart. -/
theorem original (D:Allocation G Δ Θ w)(q:Chi)(A:Stores Δ)(k:(Δ).Choices)
    (V:Config G (R.family.side d.level d.period))(x:Coarse)
    (u:Config G (R.family.side (d.level+1) d.period)→ℂ)(hu:Envelope u):
    Marked.amount T Θ P d.forest D q J₀ b u A k V=chart R d D q A k V x u:=by
  have previous:=((ManuscriptQLocalSector.bought R d D q).fixedTerm hu A k V).result
  rw [chart,Marked.amount,←previous,(permit R d D q A k V x u hu).result]

/-- The whole prescribed Gaussian supplies the fluctuation in each column.
The physical allocation, frozen Haar field, source packet, gates and
previous compact density retain exactly the same values. -/
def full (D:Allocation G Δ Θ w)(q:Chi)(A:Stores Δ)(k:(Δ).Choices)(V:Config G (R.family.side d.level d.period))
    (x:Coarse)(u:Config G (R.family.side (d.level+1) d.period)→ℂ):ℂ:=
  Marked.outside T Θ V A P d.forest J₀ (covariance R d A k) •
    ∫ Y, (∫ z, Marked.ink T Θ V k A P (shots Δ Θ) d.forest D q J₀ b (covariance R d A k)
      (fun _=>shift R d A x) u Y (z ∘ live A d.forest Θ)
      ∂Gaussian.cloud ((K).covariance d.forest k)) ∂piHaar G (Frozen A Θ d.forest)

theorem whole (D:Allocation G Δ Θ w)(q:Chi)(A:Stores Δ)(k:(Δ).Choices)
    (V:Config G (R.family.side d.level d.period))(x:Coarse)
    (u:Config G (R.family.side (d.level+1) d.period)→ℂ)(hu:Envelope u):
    Marked.amount T Θ P d.forest D q J₀ b u A k V=full R d D q A k V x u:=by
  rw [original R d D q A k V x u hu,chart,Marked.afterChange,full]
  congr 1
  apply integral_congr_ae
  filter_upwards with Y
  let ink:=Marked.ink T Θ V k A P (shots Δ Θ) d.forest D q J₀ b (covariance R d A k)
    (fun _=>shift R d A x) u Y
  have h:Integrable ink (Gaussian.cloud (covariance R d A k)):=(permit R d D q A k V x u hu).fibre Y
  have law:=projected R d A k
  change (∫ z,ink z ∂Gaussian.cloud (covariance R d A k))=_
  rw [←law.map_eq,integral_map law.measurable.aemeasurable]
  · rfl
  · erw [law.map_eq]
    exact h.aestronglyMeasurable

end YM.Integration.WilsonRootedNonflatReference
