import YM.Integration.WilsonGaussianMeasuredFourthAccuracy
import YM.Integration.WilsonScalarSourceTableDecay

/-! A single source table pays all scalar price factors before the fine level, period,
one-tree insertion and four test fields. The measured quartic then has an arbitrarily
small coupling-power error, retaining its radius and changed-root decay. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianMeasuredFourthUniform
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

private theorem scaled {g ε D x : ℝ} {n p : ℕ} (hg : 0 ≤ g) (h₁ : g ≤ 1) (cold : g ≤ ε)
    (hp : p ≤ n) (hD : 0 ≤ D) (hx : 0 ≤ x) :
    g^4*((g^n*D)*x) ≤ (ε*g^p*D)*x := by
  rw [mul_assoc (g^n) D, mul_assoc (ε*g^p) D]
  exact WilsonGaussianMeasuredFourthAccuracy.coefficient hg h₁ cold hp (mul_nonneg hD hx)

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

def At (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit) (power : ℕ) (ε : ℝ) : Prop :=
  ∀ (k : (S).Choices) (q : Chi) (t : ℝ) (z : Site c₀)
    (U : {F : Forest (S).ratio // changed S d.forest F z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀),
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G (step) (target) j₁ (table.choose j₁ j₀)
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff (target) (step).L / 4
    let c := min κ 1 / 100000
    let radial := Real.exp (-c*(radiusB θ:ℝ))
    let spatial := Real.exp (-s*(separation o z:ℝ))
    let cost := ε*g₀^power*radial
    let stored := ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o
    let shifted := ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q t Z o
    let quartic (F : Forest (S).ratio) (a b u v : E) :=
      ManuscriptQLocalGaussianQuartic.completeCoefficient R d k F o id a b u v
    0 < s ∧ 0 < c ∧
    (∀ a b u v : E, let legs := [a,b,u,v]
      |jet id stored legs 0-quartic d.forest a b u v| ≤ cost*WilsonGaussianMeasuredFourthTest.size legs ∧
      |jet id (fun B => shifted B-stored B) legs 0-(quartic U.val a b u v-quartic d.forest a b u v)| ≤
        (cost*spatial)*WilsonGaussianMeasuredFourthTest.size legs) ∧
    ∀ v : E, let observed := jet id stored [v,v,v,v] 0 / 24
      let det := g₀^4/24 * jet id (PhysicalAffineScalarSpectralRoot.halfLog T k d.forest o) [v,v,v,v] 0
      let price := (cost*‖v‖^4)/24
      |observed-(det-g₀^2/8*WilsonGaussianMeasuredFourthRay.squares R d k d.forest o v)| ≤ price ∧
      observed ≤ det+price

theorem original [Fintype I] (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
    (orders : ManuscriptQLocalStoredGaussianScalar.Paid schedule R.kit) (power : ℕ) {ε : ℝ}
    (degree : max 4 power ≤ j₁) (cold : g₀ ≤ ε) : At R d table power ε := by
  intro k q t z U Y Z o s κ c radial spatial cost stored shifted quartic
  have sold := WilsonScalarSourceTableDecay.original R d table orders.2.2 orders.1 k q t z U Y Z o
  have hg := ManuscriptQLocalIdealSquare.fine R d orders.1
  have four := (le_max_left 4 power).trans degree
  have scale (D x : ℝ) (hD : 0 ≤ D) (hx : 0 ≤ x) :
      g₀^4*((g₀^j₁*D)*x) ≤ (ε*g₀^power*D)*x :=
    scaled hg.1.le hg.2 cold ((le_max_right 4 power).trans degree) hD hx
  refine ⟨sold.1,sold.2.1,?_,?_⟩
  · intro a b u v legs
    have h := WilsonGaussianMeasuredFourthTest.tested R d orders four k q t z U Y Z o four
      sold.2.2.1 sold.2.2.2.1 a b u v
    have hsize : 0 ≤ WilsonGaussianMeasuredFourthTest.size legs :=
      Finset.prod_nonneg fun i _ => norm_nonneg (legs.get i)
    refine ⟨h.1.trans (scale radial _ (Real.exp_pos _).le hsize),h.2.trans ?_⟩
    calc g₀^4*(((g₀^j₁*radial)*spatial)*WilsonGaussianMeasuredFourthTest.size legs) =
        g₀^4*((g₀^j₁*(radial*spatial))*WilsonGaussianMeasuredFourthTest.size legs) := by ring
         _ ≤ (ε*g₀^power*(radial*spatial))*WilsonGaussianMeasuredFourthTest.size legs :=
          scale _ _ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hsize
         _ = (cost*spatial)*WilsonGaussianMeasuredFourthTest.size legs := by dsimp [cost]; ring
  · intro v observed det price
    have h := WilsonGaussianMeasuredFourthRay.measured R d orders k q t z U Y Z o v four four sold.2.2.1
    have quote := div_le_div_of_nonneg_right (scale radial (‖v‖^4) (Real.exp_pos _).le (by positivity))
      (by norm_num : (0:ℝ) ≤ 24)
    exact ⟨h.1.trans quote, h.2.trans (add_le_add_right quote _)⟩

theorem eventually (simple : G.Simple) (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
    (orders : ManuscriptQLocalStoredGaussianScalar.Paid schedule R.kit) (power : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop, ∀ {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
      (d : LocalFormal.Datum R.family Γ), b ≤ d.level → At R d table power ε := by
  have growth := (R.family.path.levels.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (max 4 power)
  obtain ⟨dg,grade⟩ := eventually_atTop.mp growth
  obtain ⟨cl,temperature⟩ := eventually_atTop.mp (WilsonGaussianMeasuredFourthAccuracy.fine R simple hε)
  filter_upwards [eventually_ge_atTop dg,eventually_ge_atTop cl] with b hd hc I eq fin Γ d later
  exact original R d table orders power (grade d.level (hd.trans later))
    (temperature d.level (hc.trans later) d.cutoff d.period d.below)

end YM.Integration.WilsonGaussianMeasuredFourthUniform
