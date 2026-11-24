import YM.Integration.ManuscriptQLocalMeasuredQuartic
import YM.Integration.ManuscriptQLocalCofinalAffineFields

/-! The complete fourth derivative of the original stored affine scalar and
the summed regular and one-site remainder, on every sufficiently late physical step. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianMeasuredFourth
open Marker Function Filter Lattice Wilson RG RG.Shoot Tree Pressure Supply
open Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open Push.PriceCompiler PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open PhysicalNext.Repeat.Legato Progress.DirectedRecipe FullQLocal.RenderedStep
open PhysicalAffineScalarFieldContraction
open PhysicalAffineScalarAperture (noHole)
open ManuscriptQLocalCofinalAffineFields (schedule)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

section Field
variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.alloy.B.a.clock.op d.level d.period
local notation "c₀" => R.alloy.B.a.clock.schedule.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "hole" => noHole S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "step" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "target" => query R.metals.p R.metals.K j₁ j₀
local notation "g₀" => Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

def At {n : ℕ → ℕ → ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit) : Prop :=
  ∀ (k : (S).Choices) (q : Chi) (t : ℝ)
    (U : ∀ z : Site c₀, {F : Forest (S).ratio // changed S d.forest F z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : ∀ z, LinkArray G (Frozen hole θ (U z).val))
    (o : Site c₀),
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G (step) (target) N r
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff (target) (step).L
    let ε := ManuscriptQLocalStoredGaussianScalar.cutAllowance G (step) (target) N r *
      Real.exp (-(κ/2)*(till θ : ℝ))
    (∀ (z : Site c₀) (a b c e : E),
      let legs := [a,b,c,e]
      let stored := ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o
      let changedStored := ManuscriptQLocalStoredGaussianScalar.stored R d k (U z).val q t (Z z) o
      let explicit (F : Forest (S).ratio) :=
        ManuscriptQLocalGaussianQuartic.completeCoefficient R d k F o id a b c e
      jet id stored legs 0 = explicit d.forest+
        g₀^4*jet id (ManuscriptQLocalScalarFields.regular R d k q t Y o) legs 0 ∧
      jet id (fun B => changedStored B-stored B) legs 0 = explicit (U z).val-explicit d.forest+
        g₀^4*jet id (ManuscriptQLocalScalarFields.changedRoot R d k q t z (U z) Y (Z z) o) legs 0) ∧
    0<s ∧ 0<κ/2 ∧ (0<g₀ ∧ g₀≤1) ∧
      Root 4 s o (fun _ : PUnit.{1} => o) (fun _ => ManuscriptQLocalScalarFields.regular R d k q t Y o)
        ((torusPay (PAC G 1) s)^4*ε) ∧
      Root 4 s o id (fun z => ManuscriptQLocalScalarFields.changedRoot R d k q t z (U z) Y (Z z) o)
        (torusPay PUnit.{1} s*(torusPay (PAC G 1) s)^4*ε)

theorem at_level [Fintype I] {n : ℕ → ℕ → ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (h₄ : 4 ≤ n j₁ j₀) : At R d p := by
  intro k q t U Y Z o
  refine ⟨fun z a b c e => ?_, ManuscriptQLocalMeasuredQuartic.price R d p k q t U Y Z o h₄⟩
  exact ManuscriptQLocalMeasuredQuartic.original R d p k q t z (U z) Y (Z z) o h₄ id a b c e
end Field

theorem eventually {G : Gauge} (R : Run G) (p : ManuscriptQLocalStoredGaussianScalar.Paid schedule R.kit) :
    ∀ᶠ b : ℕ in atTop, ∀ {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
      (d : LocalFormal.Datum R.family Γ), b ≤ d.level → At R d p := by
  have late := (R.family.path.levels.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 4
  obtain ⟨b₀,hb₀⟩ := eventually_atTop.mp late
  filter_upwards [eventually_ge_atTop b₀] with b hb
  intro I _ _ Γ d hd
  exact at_level R d p (hb₀ d.level (hb.trans hd))

end YM.Integration.WilsonGaussianMeasuredFourth
