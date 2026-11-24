import YM.Integration.FVA1Physical.MixedResets.VacuumFK
import YM.QuadraticLocal.Fk.Portal

/-!
# The published analytic action table is the RG02 cover vacuum
Exact (no torus-size tolerance in this identification!). One still pays the separate winding
bill if additionally reading off the finite-period RG02 coefficients. See `Rector.Ledger`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Filter Function Finset Lattice RG Wilson Marker Precision Tree Input
open Push Uniform Next.SectorChange
open Comparison.RG02
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped Classical Topology BigOperators
open AllOrder.Floe.Step.PlanV Pressure Gauge
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero

variable {G : Gauge} {assets : Metals G} {D : Rolls assets.p}
  {cal : Roots (G := G) assets.p.profile assets.K assets.p.kernel} {x y k : ℕ} {hx : 4 ≤ x}
  (income : Income D cal x y hx k) (card : Card D cal x y hx k)

set_option quotPrecheck false
local notation "P" => Mural.sheet assets.p D hx
local notation "K" => assets.p.kernel
local notation "O" => assets.O
local notation "C" => (assets.p.profile x).clip
local notation "𝒜" => card.self.north
local notation "T" => AllOrder.Floe.Step.tape (k+2)

local notation "F" => vacuumBill P K O 𝒜 C card.extra T (k+2)

include income
lemma action_identifies {V : Type} [Fintype V] [DecidableEq V] {J : Marker.Census V}
    {n f : Side} {S : StepData n f} (hP : S.patch = Mural.sheet assets.p D hx)
    (hK : S.kernel = assets.p.kernel)
    (hv : Larger (G:=G) S) (g : Bulk.Kernel S C 𝒜 O) (w : Bulk.Colors J G f)
    (Y : Forest S.ratio) (t : S.Choices) (z : rule (Coarse G) n) {r : ℕ} (hr : r ≤ k+2) :
    vacuumFK O 𝒜 C card.extra T (k+2) r w g Y t z = F r n z := by
  have hn : Ad G P K n := Wheel.Ride.scope_complete S hP hK hv
  have hc := kernel_exists income card hn
  have hstep := PlanV.portal D cal hx income card S hP hK hv w 𝒜 C card.extra g Y t rfl rfl rfl hr
  have hdock := PlanV.portal D cal hx income card (dock P K n) rfl rfl hn
    (Bulk.Colors.noHole G (below P n) unmarked) 𝒜 C card.extra hc.some
    (trees P K n) (label (dock P K n)) rfl rfl rfl hr
  rw [vacuumBill, dif_pos hc]
  exact (congr_fun hstep z).trans (congr_fun hdock.symm z)

theorem cover_vacuum_law {c : Side} (z : rule (Coarse G) c)
    {r : ℕ} (hr : r ≤ k+2) : (vista income.presence card r c z : ℂ) =
      coverAction P K O 𝒜 C card.extra T (k+2) r z ∧
      ∀ (S : ℕ → Side) (W : ℕ → ℕ)
        (w : ∀ i, Macrame.Window c (S i) (W i)),
        (∀ i, 0 < W i) → Tendsto (fun i => (S i).val) atTop atTop →
        Tendsto (fun i => tileAt (F r) (w i) z) atTop (𝓝 (vista income.presence card r c z : ℂ)) := by
  let fb := prePhase P K C O (fun i : Card D cal x y hx k => i.self.north)
    (fun i => i.self.paid) income.frame (fun i => i.self.upCost) assets.oga
    income.tools income.efficient Card.extra T (audited D cal x y hx) card r
  have identifies (n : Side) (hn : Ad G P K n) : (F r n) = ((↑) ∘ (fb n)) := by
    have hc := kernel_exists income card hn
    rw [vacuumBill, dif_pos hc]
    exact PlanV.portal D cal hx income card (dock P K n) rfl rfl hn
      (Bulk.Colors.noHole G (below P n) unmarked) 𝒜 C card.extra hc.some (trees P K n)
      (label (dock P K n)) rfl rfl rfl hr
  have comparison := income.revenue.earns r card hr
  haveI : Nonempty (Card D cal x y hx k) := ⟨card⟩
  have pulse := Ink.Echo.scaleLean (income.revenue.merit hr).grade card
  have hA : Often (Ad G P K) := dock_larger P K (assets.p.has P)
  exact ⟨published_eq_cover comparison pulse income.revenue.pos hA identifies z,
    fun _ _ w pos h => cover_tendsto w h pos comparison pulse income.revenue.pos hA identifies z⟩

end YM.Integration.FVA1Physical.MixedResets
