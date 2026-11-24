import YM.Integration.WilsonGaussianMeasuredFourth

/-! Testing the exact quartic identity against four arbitrary measured directions converts the
purchased derivative norm of the cutoff defect into a signed numerical error for the
independently prescribed quartic coefficient. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianMeasuredFourthTest
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

open AnalyticBridge.SectorAffine.Offset (Through)

def size {E : Type*} [Norm E] (l : List E) : ℝ := ∏ i : Fin l.length, ‖l.get i‖

theorem error_of_jet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (l : List E) (hl : l.length ≤ n) (g : ℝ) {f : E → ℝ} {C x m : ℝ}
    (law : x = m+g^4*jet id f l 0) (budget : Through n f 0 C) :
    |x-m| ≤ g^4*(C*size l) := by
  have hs : 0 ≤ size l := Finset.prod_nonneg (fun i _ => norm_nonneg (l.get i))
  have hjet : ‖jet id f l 0‖ ≤ C*size l :=
    ((iteratedFDeriv ℝ l.length f 0).le_opNorm (id ∘ l.get)).trans
      (mul_le_mul_of_nonneg_right (budget.pay _ hl) hs)
  have hg : 0 ≤ g^4 := by positivity
  rw [law,add_sub_cancel_left,abs_mul,abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left hjet hg

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

def Tested {n : ℕ → ℕ → ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (power : ℕ) : Prop :=
  ∀ (k : (S).Choices) (q : Chi) (t : ℝ) (z : Site c₀)
    (U : {F : Forest (S).ratio // changed S d.forest F z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀),
    let N := n j₁ j₀
    let r := p.2.1.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G (step) (target) N r
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff (target) (step).L/4
    let c := min κ 1/100000
    let ρ := ManuscriptQLocalStoredGaussianScalar.cutAllowance G (step) (target) N r
    let W := (max 1 (torusPay (PAC G 1) s))^N
    let geo := (|ρ| * Real.exp 1)*Real.exp (-c*(radiusB θ : ℝ))
    let C := (W*geo)*g₀^power
    let K := (torusPay PUnit.{1} s*C)*Real.exp (-s*(separation o z : ℝ))
    ∀ a b c e : E,
      let legs := [a,b,c,e]
      let stored := ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o
      let changedStored := ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q t Z o
      let quartic (F : Forest (S).ratio) :=
        ManuscriptQLocalGaussianQuartic.completeCoefficient R d k F o id a b c e
      |jet id stored legs 0-quartic d.forest| ≤ g₀^4*(C*size legs) ∧
      |jet id (fun B => changedStored B-stored B) legs 0-(quartic U.val-quartic d.forest)| ≤
        g₀^4*(K*size legs)

theorem tested [Fintype I] {n : ℕ → ℕ → ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (h₄ : 4 ≤ n j₁ j₀) (k : (S).Choices) (q : Chi) (t : ℝ) (z : Site c₀)
    (U : {F : Forest (S).ratio // changed S d.forest F z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val))
    (o : Site c₀) {m : ℕ} (hm : 4 ≤ m) {C K : ℝ}
    (hr : Through m (ManuscriptQLocalScalarFields.regular R d k q t Y o) 0 C)
    (hc : Through m (ManuscriptQLocalScalarFields.changedRoot R d k q t z U Y Z o) 0 K)
    (a b c e : E) :
    let legs := [a,b,c,e]
    let F := d.forest
    let stored := ManuscriptQLocalStoredGaussianScalar.stored R d k F q t Y o
    let changedStored := ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q t Z o
    let quartic (F : Forest (S).ratio) := ManuscriptQLocalGaussianQuartic.completeCoefficient R d k F o id a b c e
    |jet id stored legs 0-quartic F| ≤ g₀^4*(C*size legs) ∧
    |jet id (fun B => changedStored B-stored B) legs 0-(quartic U.val-quartic F)| ≤ g₀^4*(K*size legs) := by
  obtain ⟨h,h'⟩ := ManuscriptQLocalMeasuredQuartic.original R d p k q t z U Y Z o h₄ id a b c e
  exact ⟨error_of_jet [a,b,c,e] hm g₀ h hr, error_of_jet [a,b,c,e] hm g₀ h' hc⟩
end Field

end YM.Integration.WilsonGaussianMeasuredFourthTest
