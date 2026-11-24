import YM.Integration.NativeRegulatorConditionalVacuum
import YM.Integration.LocalFormalAction
import YM.Integration.SelectedPlanKineticDenominator
import YM.Comparison.RG02.Thermal.Kept

/-! Real Wilson actions, finite ground coefficients, and the signed output prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonActionConvention

open Function Filter Lattice Wilson RG Precision Exterior Tree Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep
open Comparison.RG02 Comparison.RG02.Assembly
open scoped Classical BigOperators Topology ContDiff

variable {G : Gauge}

def physicalAction (R : Run G) (N p m : ℕ) (U : Config G (R.family.side m p)) : ℝ :=
  -Real.log ((R.family.path.rep N p m).eval U)

/-- The same original conditional integral computes the action difference for every allowed field displacement. -/
theorem conditional (R : Run G) {N p m : ℕ} (hm : m < N)
    (V X : Config G (R.family.side m p)) (e : Edge (Site (R.family.side m p)) → ℝ)
    (hs : ∀ i, e i = 0 → X i = V i) :
    -Real.log ‖RG01.Kernel.generating (RG01.Kernel.expense R.family.path N m p V)
      (RG01.Kernel.channel (R.family.path.levels.clock.op m p) (R.family.path.β N p (m+1)) e V)
      (prior G (R.family.side (m+1) p)) 1 (RG01.Kernel.encoded e V X)‖ =
      physicalAction R N p m X - physicalAction R N p m V := by
  have hX := Extra.Histories.Tour.bright R.family.path R.makes.wilson N p m hm.le X
  have hV := Extra.Histories.Tour.bright R.family.path R.makes.wilson N p m hm.le V
  rw [NativeRegulatorConditionalVacuum.relative R hm V X e hs, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hX.le, Complex.norm_real, Real.norm_of_nonneg hV.le,
    Real.log_div hX.ne' hV.ne']
  unfold physicalAction
  ring

variable {V : Type} [DecidableEq V] [Fintype V] {S : Census V} {C : Family G}

def actionCoefficient (Y : Bulk.Chain C.path) (d : LocalFormal.Datum C S)
    (W : Bulk.Colors S G (C.side (d.level+1) d.period)) (r k : ℕ)
    (B : fieldDir G (C.side d.level d.period) 1) : ℂ :=
  -Symmetry.Orbit.ground (d.kernel Y) d.forest d.tag W r k B

theorem kinetic (Y : Bulk.Chain C.path) (d : LocalFormal.Datum C S)
    (W : Bulk.Colors S G (C.side (d.level+1) d.period)) (r : ℕ)
    (B : fieldDir G (C.side d.level d.period) 1) :
    actionCoefficient Y d W r 0 B =
      ↑(jet (fun A : fieldDir G (C.side d.level d.period) 1 =>
        mainTerm (C.path.rep d.cutoff d.period d.level).clip
          (C.path.rep d.cutoff d.period d.level).path (represent A)) 2 B) := by
  unfold actionCoefficient
  rw [Adjacent.LocalScript.precedence, Symmetry.price,
    Thermal.maps Y d.cutoff d.level d.period d.below d.forest d.tag, neg_neg]

theorem positive (R : Run G) (hG : G.Simple) (hR : ActualRunNativeComponentRecipe.Attached R)
    (d : LocalFormal.Datum R.family S) (hm0 : 0 < d.level)
    (W : Bulk.Colors S G (R.family.side (d.level+1) d.period)) (r : ℕ) :
    (0 : ℝ) < (actionCoefficient (RunFormalChain.fromRun R) d W r 0
      (NativeNormalizedBondTest.actualField R hG d.level d.period)).re := by
  rw [kinetic, Complex.ofReal_re]
  have hc : R.family.path.Conv d.cutoff d.period d.level :=
    R.makes.wilson.represents d.cutoff d.period d.level d.below.le
  rw [hc.clip]
  exact (SelectedPlanKineticDenominator.denominator R hG hR d.cutoff d.level d.period d.below hm0).1

/-- Every positive-order action coefficient is the negative of the original quiet logarithmic coefficient. -/
theorem higher (Y : Bulk.Chain C.path) (d : LocalFormal.Datum C S)
    (r k : ℕ) (hk : k ≠ 0) (B : fieldDir G (C.side d.level d.period) 1) :
    actionCoefficient Y d d.colors r k B =
      -({d with field := B} : LocalFormal.Datum C S).vacuumLogCoefficient Y r k S.quiet :=
  congrArg Neg.neg (d.vacuumAction_nonzero Y r k hk B)

/-- The finite ground read uses the complete original datum and its own leading stationary price. -/
theorem covered (Y : Bulk.Chain C.path) (d : LocalFormal.Datum C S) (r : ℕ) (g : ℝ) :
    -(Adjacent.cover (d.vacuumAction Y r) r g d.field).re =
      -(Symmetry.price (d.kernel Y) d.forest d.tag d.field).re -
        Order.exponentPrice (d.raw Y r) g := by
  rw [d.vacuumAction_cover Y r g]
  ring

/-- The outgoing positive-action prescription on the actual chosen kinetic plan. -/
structure SignedOutput (Y : Bulk.Chain C.path) (J : Request V) (d : LocalFormal.Datum C S)
    (colors : TestSpace J.tests → Bulk.Colors S G (C.side (d.level+1) d.period))
    (P : Plan C d.cutoff d.period J.order) where
  extension : ℝ → fieldDir G (C.side d.level d.period) 1 → ℂ
  value (B : fieldDir G (C.side d.level d.period) 1) :
    ∀ᶠ g : ℝ in 𝓝[>] 0, extension g B =
      (modelAction P d.level g (represent (g • B)) : ℂ)
  smooth (B : fieldDir G (C.side d.level d.period) 1) :
    ContDiffAt ℝ J.order (fun g => extension g B) 0
  scalar : ℕ → ℂ
  prescribed (x : TestSpace J.tests) (B : fieldDir G (C.side d.level d.period) 1)
      (k : ℕ) (hk : k ≤ J.order) :
    jet (fun g => extension g B) k 1 = actionCoefficient Y d (colors x) J.order k B + scalar k

theorem SignedOutput.centered {Y : Bulk.Chain C.path} {J : Request V} {d : LocalFormal.Datum C S}
    {colors : TestSpace J.tests → Bulk.Colors S G (C.side (d.level+1) d.period)}
    {P : Plan C d.cutoff d.period J.order} (h : SignedOutput Y J d colors P)
    (x : TestSpace J.tests) (B : fieldDir G (C.side d.level d.period) 1) (k : ℕ) (hk : k ≤ J.order) :
    jet (fun g => h.extension g B) k 1 - jet (fun g => h.extension g 0) k 1 =
      Symmetry.Orbit.ground (d.kernel Y) d.forest d.tag (colors x) J.order k 0 -
        Symmetry.Orbit.ground (d.kernel Y) d.forest d.tag (colors x) J.order k B := by
  rw [h.prescribed x B k hk, h.prescribed x 0 k hk]
  unfold actionCoefficient
  abel

end YM.Integration.PhysicalWilsonActionConvention
end
