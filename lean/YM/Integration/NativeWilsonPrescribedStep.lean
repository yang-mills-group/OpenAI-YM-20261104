import YM.Integration.NativeWilsonColoredMeasure
import YM.Integration.NativeWilsonGeneratorAgreement

/-! Original finite Wilson denominator, ordinary marked moment and prescribed connected coefficient
on the same original RG kernel, forest, tag and collection of charged colors. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeWilsonPrescribedStep
open Function Filter Lattice Wilson RG Precision Tree Exterior Marker Multi
open PhysicalNext.Repeat.Legato RegulatorIR RegulatorIR.FVAAlt2
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Integral Comparison.RG02.Actual
open Comparison.RG02.Order
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {H : Census V}
    (R : Run G) (m p : ℕ)
local notation "S" => R.family.path.levels.clock.op m p
local notation "K" => (RunFormalChain.fromRun R).step (m+1) m p (Nat.lt_succ_self m)
local notation "Y" => RunFormalChain.fromRun R
variable (F : Forest (R.family.path.levels.clock.op m p).ratio)
    (j : (R.family.path.levels.clock.op m p).Choices)
    (W : Bulk.Colors H G (R.family.side (m+1) p))
    (x : fieldDir G (R.family.side m p) 1) (r : ℕ)

def datum : LocalFormal.Datum R.family H := ⟨m+1,p,m,Nat.lt_succ_self m,F,j,W,x⟩
local notation "D" => datum R m p F j W x
local notation "Q" => NativeWilsonColoredMeasure.colors R m p W

/-- The source includes all ordinary products of charged marked components.
Its real vacuum is the original Wilson law for every configuration. -/
theorem unmasked (t : ℝ) (U : Config G (R.family.side (m+1) p)) :
    Bare.top Q t U = Complex.ofReal (Wilson.bare (Integral.temperature t) U) • Bare.Passes W t U := rfl

def measured (t : ℝ) := Bare.realMoment K F Q j x t

/-- A genuine finite measured vector has the original prescribed Wick coefficients. -/
theorem first (hw : Bulk.Well W) (hf : Bare.Starts W)
    (hflat : Assembly.GradeAt (r+3) (Bulk.projected (fun g U => (Q).vac g U - W.vac g U))) :
    Laplace.Fleet.Test ((D).ordinary Y r) (fun t => Order.unitScale (measured R m p F j W x t)) ∧
    Laplace.Fleet.Test ((D).markedLog Y r) (fun t =>
      Extra.Trajectories.connected (Order.unitScale (measured R m p F j W x t))) := by
  have hwq := NativeWilsonColoredMeasure.well R m p W hw
  have h0 := NativeWilsonGeneratorAgreement.of_grade K F j Q W.vac x r hwq
    (show Bulk.Well (NativeWilsonGeneratorAgreement.replaceVacuum Q W.vac) from hw) hflat
  have hraw : Bulk.Fk K F j Q x r = (D).raw Y r := h0
  obtain ⟨_,_,hn,hm⟩ := Bare.wilson_step_test K F Q j x r (R.family.path.levels.budget m)
    (NativeWilsonColoredMeasure.witnessed R m p W hw hf)
  unfold LocalFormal.Datum.ordinary LocalFormal.Datum.markedLog
  rw [←hraw]
  exact ⟨hn,hm⟩

end YM.Integration.NativeWilsonPrescribedStep
end
