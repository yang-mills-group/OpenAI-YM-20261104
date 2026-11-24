import YM.Integration.WilsonMatrixTicketLanesVacuumKept

/-! The complete earlier signed hard density in the original normalized
Wilson kernel after the regular cut, tested by any retained joint field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesVacuumKeptKernel
open Function Filter MeasureTheory Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato IterationFour.Vacuum PhysicalWilsonConditionalRestriction
open WilsonMatrixTicketLanesVacuumKept WilsonInvariantActionRegisteredHearing
open private factor_receipt from YM.Integration.OriginalMarkedRunAction
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p m:ℕ} (interior:m+1<N) (d:ℕ)
local notation "original" => R.family.path.rep N p (m+1)
local notation "lower" => R.family.path.rep N p m
local notation "cut" => OriginalMarkedRunAction.approximation R (p:=p) interior d
local notation "remainder" => OriginalMarkedRunAction.remainder R (p:=p) interior d
local notation "j" => m+1
local notation "fine" => Config G (R.family.side j p)
local notation "base" => Config G (R.family.side m p)
local notation "joint" => actualConditionalDensity R.family N p m

theorem density (h:OriginalMarkedRunAction.Comparison R (p:=p) interior d)
    (w:Finset ℕ → fine → ℝ) (V:base) (U:fine):
    joint V U*normalized cut w U=
      (R.family.path.levels.clock.op m p).density (R.family.path.β N p j) U V*Real.exp (-(remainder).additive (R.alloy.B.a.budget j) U)*Real.exp ((cut).exponent U)*restricted cut w U/(lower).eval V:=by
  let S:=ActualRunSpring.selected R N p j interior
  have factor:=(factor_receipt R interior S d h.posterior U)
  have positive:0<(original).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson (p:=p) interior.le U
  have nonzero:(cut).eval U≠0:=by
    intro hzero
    rw [factor,hzero,zero_mul] at positive
    exact (lt_irrefl 0) positive
  change ((R.family.path.levels.clock.op m p).density (R.family.path.β N p j) U V*(original).eval U/(lower).eval V)*
    (Real.exp ((cut).exponent U)*restricted cut w U/(cut).eval U)=_
  rw [factor]
  calc
    _=((R.family.path.levels.clock.op m p).density (R.family.path.β N p j) U V*Real.exp (-(remainder).additive (R.alloy.B.a.budget j) U)*Real.exp ((cut).exponent U)*restricted cut w U/(lower).eval V)*
        ((cut).eval U*((cut).eval U)⁻¹):=by ring
    _=_:=by rw [mul_inv_cancel₀ nonzero,mul_one]

/-- In particular, this is the original deposited numbered hard source.
The test can be the empty, singleton or mixed marked field at the same V. -/
theorem table {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (h:OriginalMarkedRunAction.Comparison R (p:=p) interior d) (i:ℕ) (V:base) (test:fine→Y):
    (∫U,(joint V U*(score R interior (hard R interior i)).val (V,U)) • test U ∂prior G (R.family.side j p))=
      ∫U,((R.family.path.levels.clock.op m p).density (R.family.path.β N p j) U V*Real.exp (-(remainder).additive (R.alloy.B.a.budget j) U)*Real.exp ((cut).exponent U)*
        occurrence cut i U/(lower).eval V) • test U ∂prior G (R.family.side j p):=by
  apply integral_congr_ae
  apply ae_of_all
  intro U
  dsimp only
  rw [hearing R interior d i V U,density R interior d h _ V U,marked cut i U]

end YM.Integration.WilsonMatrixTicketLanesVacuumKeptKernel
