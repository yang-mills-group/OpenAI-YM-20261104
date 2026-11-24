import YM.Integration.WilsonConditionalTaylorBulkHistory
import YM.Integration.WilsonConditionalTaylorFieldBalance
import YM.Integration.WilsonConditionalTaylorKineticWrap
import YM.Integration.WilsonMovingInitialAction

/-! The unrebooked finite field and grades/head/Ward inventory, the
original compact ultraviolet endpoint, and the original finite sample grant. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorCourseLedger
open Filter Function PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free
open PhysicalNext.Repeat.Legato MSbar MSbar.Rolling MSbar.Midpoint
open WilsonConditionalTaylorBulkShape WilsonConditionalTaylorBulkHistory WilsonConditionalTaylorFieldBalance
open WilsonMovingPolynomialPull
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (u : G.ColorIndex)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n, (primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

theorem rawField (N j : ℕ) (hi : j<N) (n : Side) :
    let Z:=raw R wood tags N j (course R u wood tags N (j+1)) n
    coeff 0 Z=crunch (kernelP G R.family.path.levels.clock.kernel.penalty (location R.family.path.levels N j) n) ∧
        Ranks Z ∧ Civic Z :=by
  intro Z
  let V:=R.family.path.levels
  let K:=RunFormalChain.fromRun R
  let P:=destination V N j
  have pre:=admitted R u wood tags N (j+1) hi (n*P.L)
  rw [loc_land _ N j hi]
  exact ⟨Reef.landed_cost P R.metals.O (V.blocks j 0).branches (wood j) n (tags j n) _ pre.1 K.receipt (V.clock.adm j),
    WilsonConditionalTaylorBulkShape.output P (wood j) R.metals.O (V.blocks j 0).branches n (tags j n) _ K.receipt (V.clock.adm j) pre.2.1 pre.1,
    Reef.landed_ward P R.metals.O (V.blocks j 0).branches (wood j) n (tags j n) _ pre.1 K.receipt (V.clock.adm j) pre.2.2⟩

theorem opening (N : ℕ) (n : Side) :
    Rolling.opening G n = splitV (place (WilsonMovingGaussianCoordinates.link G n).symm (course R u wood tags N N n)) :=by
  rw [ultraviolet,WilsonMovingInitialAction.original]
  unfold WilsonMovingBareVacuum.released WilsonMovingBareVacuum.seed place splitV
  rw [Mesa.top_word]

theorem sampled (N : ℕ) : ∀ᶠ per:ℕ in atTop, ∀ j ≤ N, Alto.Sampled (R.family.side j per) (R.family.path.levels.params j) :=by
  have money (j : ℕ) : ∀ᶠ per:ℕ in atTop,Alto.Sampled (R.family.side j per) (R.family.path.levels.params j):=by
    let V:=R.family.path.levels
    have due:=(UVNext.PricedKernels.Echo.schedule_sides V.S j).eventually (Alto.retreat (V.params j))
    filter_upwards [due] with i hi
    exact hi (R.family.side j i) rfl
  have all:=(Finset.range (N+1)).eventually_all.mpr (fun i _=>money i)
  exact all.mono (fun _ h j hj=>h j (Finset.mem_range.mpr (by omega)))

end YM.Integration.WilsonConditionalTaylorCourseLedger

