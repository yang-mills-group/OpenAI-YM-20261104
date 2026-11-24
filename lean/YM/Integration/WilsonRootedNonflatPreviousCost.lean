import YM.Integration.WilsonRootedNonflatPreviousSite
import YM.Integration.WilsonRootedNonflatIncome

/-! A financial statement before the sectioning of any coarse field:
the whole previous signed kinetic and every earlier finite-spring term
at the issued original site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatPreviousCost
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open IterationFour IterationFour.Vacuum WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open OriginalMarkedRunAction WilsonLimitConstruction
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "Tj" => R.family.path.levels.params (d.level+1)
local notation "α" => R.alloy.B.kin.alpha d.cutoff (d.level+1)

def letter (r:ℕ)(Z:SeriesA G)(o:Site fine)(U:Config G fine):ℝ:=
  -(α*secondAt (Tj).clip (P).path o U+springAt R d.cutoff d.period (d.level+1) r Z g o U)

def bill (r:ℕ)(Z:SeriesA G)(b:ℝ):ℝ:=
  |α| * quadraticBill (Tj).clip (Tj).paths+springSiteBill R d.cutoff (d.level+1) r Z g b

theorem invoice (r:ℕ)(Z:SeriesA G){σ b:ℝ}(hs:0<σ)(draw:Draw Z σ b)(o:Site fine):
    Envelope (letter R d r Z o) ∧ GaugeInvariant (letter R d r Z o) ∧ ∀U,‖letter R d r Z o U‖≤bill R d r Z b:=by
  have hc:R.family.path.Conv d.cutoff d.period (d.level+1):=R.makes.wilson.represents d.cutoff d.period (d.level+1) d.below
  have hp:(P).path.Bounds (Tj).clip (Tj).width (Tj).paths (R.family.path.levels.clock.loopCap (d.level+1)):=by
    rw [←hc.clip]
    exact hc.good.paths
  have k:=bare_site_price hp o
  have s:=filed_site_price R d.cutoff d.period (d.level+1) r d.below Z hs draw g o
  have knee:Envelope (secondAt (Tj).clip (P).path o):=⟨k.1,_,k.2.1⟩
  have spring:Envelope (springAt R d.cutoff d.period (d.level+1) r Z g o):=⟨s.1,_,s.2⟩
  refine ⟨(((Envelope.const _).mul knee).add spring).neg,?_,fun U=>?_⟩
  · have inv:=(WilsonRootedNonflatPreviousSite.springs R d.cutoff d.period (d.level+1) r d.below Z draw g o).2
    exact fun h U=>congrArg Neg.neg (inv h U)
  · unfold letter bill
    rw [norm_neg]
    refine (norm_add_le _ _).trans (add_le_add ?_ (s.2 U))
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (k.2.1 U) (abs_nonneg _)

theorem columns (r:ℕ)(Z:SeriesA G){σ b:ℝ}(hs:0<σ)(draw:Draw Z σ b)(o:Site fine)
    (V:Config G coarse)(incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming)
    (s:Γ.Mode){fee:ℝ}(cost:∀U,‖Actual.atMark s incoming U‖≤fee*(P).eval U):
    ‖(Δ).push (P).beta (Actual.atMark s incoming) V/((P₀).eval V:ℂ)‖≤fee ∧
    ‖(Δ).push (P).beta (fun U=>(letter R d r Z o U:ℂ)*Actual.atMark s incoming U) V/((P₀).eval V:ℂ)‖≤bill R d r Z b*fee:=by
  have hx:=invoice R d r Z hs draw o
  refine ⟨WilsonRootedNonflatIncome.spend R d V _ (floor.safe s) cost,
    WilsonRootedNonflatIncome.spend R d V _ (hx.1.ofReal_env.mulC (floor.safe s)) (fun U=>?_)⟩
  rw [norm_mul,Complex.norm_real]
  calc
    _≤bill R d r Z b*(fee*(P).eval U):=mul_le_mul (hx.2.2 U) (cost U) (norm_nonneg _) ((norm_nonneg _).trans (hx.2.2 U))
    _=_:=by ring

end YM.Integration.WilsonRootedNonflatPreviousCost
