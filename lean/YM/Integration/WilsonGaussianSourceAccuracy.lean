import YM.Integration.WilsonGaussianSourceProfiles
import YM.Integration.WilsonRootedPhysicalSpringAccurateMS
import YM.Integration.WilsonGaussianMeasuredFourthTest

/-! The exact finite coefficient at each order and its measured error on the original forest. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianSourceAccuracy
open Marker Function Filter Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open Push.PriceCompiler PhysicalNext.JointLoad PhysicalAffineScalarIdealSquare PhysicalAffineScalarFieldContraction
open PhysicalAffineScalarAperture (noHole)
open ManuscriptQLocalCofinalAffineFields (schedule)
open AnalyticBridge.SectorAffine.Offset (Through)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.alloy.B.a.clock.op d.level d.period
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.alloy.B.a.clock.schedule.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "hole" => noHole S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "step" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "target" => query R.metals.p R.metals.K j₁ j₀
local notation "g₀" => Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

def At (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
    (through power : ℕ) (ε : ℝ) : Prop :=
  ∀ (k : (S).Choices) (q : Chi) (t : ℝ) (z : Site c₀) (U : {F : Forest (S).ratio // changed S d.forest F z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀),
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G (step) (target) j₁ (table.choose j₁ j₀)
    let c := min (ManuscriptQLocalScalarClockPurchase.cutoff (target) (step).L/4) 1/100000
    let C := (ε*g₀^power)*Real.exp (-c*(radiusB θ:ℝ))
    let K := C*Real.exp (-s*(separation o z:ℝ))
    0<s ∧ 0<c ∧ ∀ (l : List E), l.length ≤ through →
      |jet id (ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o) l 0-
        WilsonGaussianSourcePolynomial.polynomial R d k d.forest o id l g₀| ≤ C*WilsonGaussianMeasuredFourthTest.size l ∧
      |jet id (fun B => ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q t Z o B-
          ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o B) l 0-
        (WilsonGaussianSourcePolynomial.polynomial R d k U.val o id l g₀-
          WilsonGaussianSourcePolynomial.polynomial R d k d.forest o id l g₀)| ≤ K*WilsonGaussianMeasuredFourthTest.size l

theorem original [Fintype I] (orders : ManuscriptQLocalIdealSquare.Paid schedule R.kit)
    (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit) {through power : ℕ} {ε : ℝ}
    (height : through ≤ j₁) (actual : WilsonRootedPhysicalSpringAccurateMS.Fields R d table through power ε) :
    At R d table through power ε := by
  intro k q t z U Y Z o s c C K
  obtain ⟨hs,hc,_,_,ordinary,changed⟩ := actual k q t z U Y Z o
  refine ⟨hs,hc,?_⟩
  intro l hl
  exact WilsonGaussianSourceProfiles.tested R d orders k q t z U Y Z o height ordinary changed id l hl

end YM.Integration.WilsonGaussianSourceAccuracy
