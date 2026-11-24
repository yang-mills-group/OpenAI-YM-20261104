import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalTrial
import YM.Integration.PhysicalWilsonBornMaterial

/-! The absolute Haar normalization of the first physical Q experiment at varying temperature. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalMeasure
open Function Filter Lattice Wilson RG Precision Tree Marker Multi Exterior
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Actual Pert.Asymptotics WilsonLimitConstruction
open scoped Classical Topology BigOperators

theorem normalized {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {c f:Side}
    {S:StepData c f} {p:Clip} {path:PathData G} {O:ChartRatio G} (K:Bulk.Kernel S p path O)
    (F:Forest S.ratio) (W:Bulk.Colors Γ G f) (tag:S.Choices) (a:fieldDir G c 1)
    (s:Γ.Mode) {h:ℝ} (positive:0<h):
    (Order.unitScale (Bare.realMoment K F W tag a h)).part s=
      (S.push (Integral.temperature h) (bare (Integral.temperature h)) (Integral.sample h a))⁻¹ •
        S.push (Integral.temperature h) (fun U=>bare (Integral.temperature h) U • (Bare.Passes W h U).part s)
          (Integral.sample h a):=by
  rw [Order.unitScale,Poly.part_smul,Bare.vacancy,Bare.realMoment,Poly.part_smul,grades]
  have off:(Integral.office K F tag h 0 a:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Integral.office_pos K F tag h 0 a positive).ne'
  change ((Bare.rho K F tag a h : ℝ):ℂ)⁻¹*(((Integral.office K F tag h 0 a:ℂ)⁻¹)*_)=_
  simp only [Bare.rho,Complex.ofReal_mul,Complex.ofReal_inv,mul_inv_rev,inv_inv,
    Complex.real_smul]
  have release (x:ℂ):(Integral.office K F tag h 0 a:ℂ)*((Integral.office K F tag h 0 a:ℂ)⁻¹*x)=x:=by
    rw [←mul_assoc,mul_inv_cancel₀ off,one_mul]
  simp only [mul_assoc,release]
  congr 2

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  (profile:∀k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
  (hm:ActualOriginalQInitialInput.start R hG u J A profile≤d.level)
  (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "W" => FundedMatchedPointOpening.colors R hG u J A d Q o μ orders profile hm hp
local notation "K" => (RunFormalChain.fromRun R).step (d.level+1) d.level d.period (Nat.lt_succ_self _)
local notation "S" => R.family.path.levels.clock.op d.level d.period

theorem physical (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) (s:(Stock.census V).Mode) {h:ℝ} (positive:0<h):
    (Order.unitScale (Bare.realMoment (K) F (W t) tag a h)).part s=
      ((S).push (Integral.temperature h) (bare (Integral.temperature h)) (Integral.sample h a))⁻¹ •
        (S).push (Integral.temperature h) (fun U=>bare (Integral.temperature h) U •
          (Poly.pass ((ActualOriginalQInitialInput.packets R hG u J A d Q o μ orders).read t h U)).part s)
          (Integral.sample h a):=by
  rw [normalized (K) F (W t) tag a s positive]
  simp only [Bare.Passes,PhysicalWilsonBornMaterial.charged R hG u J A d Q o μ orders profile hm hp t h positive.ne']

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalMeasure
