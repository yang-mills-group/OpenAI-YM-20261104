import YM.SignedWilsonExpansion.Public.World
/-!
# Original Wilson data in `World.Construction`

The selected run uses the whole-product course with support exponent 100.
Its variable-house and optical estimates are on that same run. The cutoff
file starts with the bare density, and the coarse readings use the density
inherited from that file. `chargedPenalty` identifies the real kernel
penalty. `variable_stage_here` proves that the `Tracks.readings` stage
condition is incompatible with the elected exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Answer.ContinuumLimit.Construction
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open OPE.Therm QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule WilsonOriginalCollarElection ThroughLaunch
open scoped Classical
universe u
variable {G:Gauge} {Z:Family G} {H:G.Simple} {ε:ℝ} {O:OrderS G} {e: Axis} (E:Construction.{u} H ε e O)

-- `ε` is the kernel penalty NOT a cost hypothesis about the continuum fields.
lemma original_selected : E.paths.family.path.Selected := E.paths.makes.wilson
lemma chargedPenalty : E.paths.family.path.levels.clock.kernel.penalty=ε := E.receipts.receiptsP.1.1
lemma shelf_here : House (teacher (prepared O)) H WilsonOriginalAllOrderCourse.law E.paths ∧
      WilsonLimitConstruction.FundedOriginalProperties.{u} H ε E.pillars :=⟨ E.receipts.paid.house,E.receipts.receiptsP.1 ⟩
lemma support_exponent_original (i:ℕ) : (E.paths.family.path.levels.budget i).supportExponent=100 := E.receipts.paid.support i
lemma variable_stage_here : ¬ WithStage E.paths.metals.p Tracks.readings:=by
    intro x
    obtain ⟨i,v⟩:= ( E.paths.alloy.B.a.fits.deep.eventually_ge_atTop 1 ).exists
    have ht:= x.prices ( E.paths.alloy.B.a.clock.J i ); have p:= support_exponent_original E i
    have hx:0 < ( ( E.paths.alloy.B.a.clock.J i ):ℝ ) := Nat.cast_pos.mpr v
    change _= 100+(( _ ):ℝ) at ht -- syntax?a
    change ( E.paths.alloy.B.a.params i ).supportExponent=100 at p
    rw [ Push.PriceCompiler.params_eq E.paths.alloy.B.valid i, ht ] at p; linarith
end YM.Answer.ContinuumLimit.Construction
