import YM.Integration.WilsonMatrixTicketLanesNativeFields
import YM.Integration.WilsonCoherentTerminalFrame

/-! Complete nonlinear Wilson observables with the actual matched finite Wick compensator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesCompensatedFields
open FVA2 MS.Local.Physical Wilson Lattice RGComparison.Core16 RGComparison.Core16.Spool
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesNativePrices
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (B : Deck G) (N p : ℕ)

/-- File the independent compensated coordinates using the actual terminal field registration. -/
def field (d k : ℕ) (u : B.BIndex (d:ℤ) k) : R.family.label d :=
  (R.family.factory d N p).terminal ((warehouse R).qfits B d k u)

/-- The source prices are constant before both regulators. Each true angle and engineering factor remains present. -/
def price (d k : ℕ) (u : B.BIndex (d:ℤ) k) (j : (R.family.labels.level d).Index) : ℂ :=
  (((R.family.path.levels.clock.threshold N)⁻¹ ^ ((R.family.labels.level d).grades j).2 : ℝ):ℂ) *
    (((R.family.S.a N : ℂ)^d)⁻¹ * FVAAlt2.Shop.valueP B (R.family.localSection d)
      (R.makes.sections d) (CoefficientBridge.run_valuation R d) u j)

theorem coordinates (d k : ℕ) (u : B.BIndex (d:ℤ) k) (j : (R.family.labels.level d).Index) :
    WilsonCoherentTerminalFrame.coordinates R N p (field R B N p d k u) j = price R B N d k u j := by
  unfold WilsonCoherentTerminalFrame.coordinates field price
  rw [LinearEquiv.symm_apply_apply,Labels.Frame.scaled_apply]
  have he := ((warehouse R).price_cast B u j).symm.trans (WilsonMatrixTicketLanesNativePrices.original R B d k u j)
  exact congrArg (fun z : ℂ => (((R.family.path.levels.clock.threshold N)⁻¹ ^
    ((R.family.labels.level d).grades j).2 : ℝ):ℂ) * (((R.family.S.a N:ℂ)^d)⁻¹*z)) he


/-- The actual nonlinear group observable for this independent MS label at every cutoff and torus. -/
theorem original (d k : ℕ) (u : B.BIndex (d:ℤ) k) (x : Site (R.family.side N p))
    (U : Config G (R.family.side N p)) :
    R.family.O N p (field R B N p d k u) x U = ∑ j,
      price R B N d k u j * Light (WilsonCoherentTerminalFrame.lamp R d j) (R.family.side N p) x U := by
  rw [WilsonCoherentTerminalFrame.row]
  simp_rw [coordinates]

/-- One common physical configuration for all the independently submitted fields and arbitrary centers. -/
theorem centered {I : Type} [Fintype I] (d k : I → ℕ) (u : ∀ i, B.BIndex ((d i):ℤ) (k i))
    (x : I → Site (R.family.side N p)) (c : I → ℂ) (U : Config G (R.family.side N p)) :
    (∏ i, (R.family.O N p (field R B N p (d i) (k i) (u i)) (x i) U-c i)) =
    ∏ i, ((∑ j, price R B N (d i) (k i) (u i) j *
      Light (WilsonCoherentTerminalFrame.lamp R (d i) j) (R.family.side N p) (x i) U)-c i) := by
  simp_rw [original]

end YM.Integration.WilsonMatrixTicketLanesCompensatedFields
