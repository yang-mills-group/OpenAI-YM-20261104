import YM.Integration.WilsonPosteriorProjectionPinned
import YM.Integration.FVA1Physical.Round2.RootedFieldTrajectory

/-! A funded original per-label root menu supplies every specified true
field derivative after its numerical archive cut has been reached. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionRootedSchedule
open Function Filter Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open MSbar MSbar.Heath FVA1Physical.Wilson FVA1Physical.Round2.Curvature FVA1Physical.Marked
open WilsonPosteriorProjectionPinned RGComparison.Core16.Spool
open scoped Classical Topology BigOperators
variable {G : Gauge}

/-- Prebooking a given original list at a finite stage gives every local
root charge for that same list after its own (rank-dependent) output stage. -/
theorem charge {I : Type} [Fintype I] {d : ℕ} (a : I → CoverLabel G d) (R : Run G)
    (cash : Late R (rootedFieldMenu a)) (q s radius h : ℕ) :
    LateThreshold R (chargeGate a q s radius (margin_pos h)) := by
  obtain ⟨level,funds⟩ := eventually_atTop.mp cash
  let demand := q+s+radius+h
  filter_upwards [eventually_ge_atTop (R.t demand),eventually_ge_atTop level] with k cut late j kj n
  let H := R.alloy.B.a.params j
  let H' := R.alloy.B.a.params (j+1)
  let P := (R.alloy.B.a.clock.op j n).patch
  let K := (R.alloy.B.a.clock.op j n).kernel
  have ord : demand ≤ H.order :=
    (Nat.le_succ demand).trans (((R.makes.stages demand).2 j (cut.trans kj)).1)
  dsimp only [demand] at ord
  let i : ReadingInputs H.order := (⟨q,by omega⟩,⟨s,by omega⟩,⟨radius,by omega⟩,⟨h,by omega⟩,false)
  let fee := fun i : ReadingInputs H.order =>
    chargeGate a i.1 i.2.1 i.2.2.1 (margin_pos i.2.2.2.1) H H' P K
  exact (le_abs_self (fee i)).trans
    ((Finset.single_le_sum (fun x (_ : x ∈ Finset.univ) => abs_nonneg (fee x))
      (Finset.mem_univ i)).trans (funds j (late.trans kj) n))

end YM.Integration.WilsonPosteriorProjectionRootedSchedule
end

