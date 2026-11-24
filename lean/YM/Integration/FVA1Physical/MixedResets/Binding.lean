import YM.Integration.FVA1Physical.MixedResets.Aggregate
import YM.QuadraticLocal.Fk.Ports

/-!
# Tie the publisher used by the actual two resets to the cover law, not just seam prices

As a corollary get the formal identification in the whole mask at the
purchased order, not taking each epoch at coincident probes.
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
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn
open scoped Classical Topology BigOperators
open AllOrder.Floe.Step.PlanV Pressure Gauge
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero


private theorem byBill {c f : Side} (S : StepData c f) {G : Gauge}
    (O : ChartRatio G) (action : PathData G) (clip : Clip) (U : Layout G) (extra : Finset Age)
    {V ι α : Type} [DecidableEq V] {I : Marker.Census V} {passport : Passport f V}
    (M : ι → Row passport I G α) (P : Patch) (K : KernelChoices) (hP : S.patch = P)
    (hK : S.kernel = K) (u : Club M) (p r : ℕ) (off : Club.Keys M u → Site P.L)
    (loc : ∀ j : Club.Keys M u, QuadraticLocal.Echo.Sara.seat P S hP off j (Club.site M u S.ratio j) =
      (Club.troops M u j).center) :
    let f (L : Patch) (K : KernelChoices) (off : Club.Keys M u → Site L.L) :=
      connectedBill K O action clip U extra (fun i => (Club.troops M u i).lamp)
        (fun i => (Club.troops M u i).atom) L off p r
    f S.patch S.kernel (clubOffset S M u) = f P K off := by
  subst P K
  intro F
  rw [show off = clubOffset S M u from ?_]; funext j
  exact (S.ratio.assemble_res (Club.site M u S.ratio j, off j)).symm.trans
    (congr_arg S.ratio.residue (loc j))

variable {V ι α : Type} [Fintype V] [DecidableEq V] {G : Gauge}
  {X : Metals G} {c f : Side} {m : ℕ} {φ : ℕ → ℕ}
  (pay : Roots (G:=G) X.p.profile X.K X.p.kernel) (D : Rolls X.p) (Q : pay.Tab D)
  (R : Alloy X D) (u : f.val = c.val*(R.B.a.S.block m).val)

set_option quotPrecheck false
local notation "L" => panel R m u
local notation "x" => R.B.a.clock.J (m+1)
local notation "y" => R.B.a.clock.J m
local notation "P" => Mural.sheet X.p D (R.B.a.clock.adm (m+1))
local notation "C" => (X.p.profile x).clip
variable (capacity : Opportunity (R.B.a.clock.J (m+1)) (R.B.a.clock.J m))
  (E : Epoch pay D (R.B.a.clock.J (m+1)) (R.B.a.clock.J m) capacity) (card : Card D pay (R.B.a.clock.J (m+1)) (R.B.a.clock.J m) E.wants (Burn.horizon E.vac))
  (clock : Offices.Books pay D Q φ) {p : ℕ} {J : Passport f V} {I : Marker.Census V}
  (M : ι → Row J I G α)
  (v : Cruise.Voter M (Poetry.Agenda.seed pay φ (Burn.horizon E.vac) (R.B.a.clock.J (m+1))) p capacity.count capacity.stage E.vac (R.B.a.clock.J m))
  (ad : Larger (G:=G) (panel R m u))

include ad clock v

local notation "𝒮" => Cruise.publish pay D Q R φ clock capacity E u M p v card
local notation "r₀" => Burn.horizon E.vac+2
local notation "T" => AllOrder.Floe.Step.tape r₀
local notation "K" => X.p.kernel
local notation "𝒜" => card.extra
local notation "O" => X.O
local notation "𝒫" => card.self.north

namespace CP5Bridge
set_option maxHeartbeats 800000

theorem writes : PressWrites M 𝒮 L O 𝒫 C 𝒜 T := by
  intro cluster r h z
  let ticket := Cruise.ticket pay D R φ capacity E M cluster p v
  let issue := clock.lore x y capacity E ticket
  let stencil := Cruise.rules pay D R φ capacity E u M cluster p v
  let pins := Aperture.Bunch.mapC (Club.site M cluster ((panel R m u).ratio))
  let arg := Mentor.artifact pay D R φ capacity E ticket stencil card
  haveI : Nonempty (Card D pay x y E.wants (Burn.horizon E.vac)) := ⟨card⟩
  haveI : Nonempty (Mentor.Params pay D φ x y E.wants ticket.val.loans E.vac) := ⟨arg⟩
  have accepts :  Ad G P K c := Wheel.Ride.scope_complete (panel R m u)
    (Plateau.Line.patch_here R u) R.B.valid.kernel ad
  have near : ∀ j : Club.Keys M cluster, QuadraticLocal.Echo.Sara.seat P L (Plateau.Line.patch_here R u) stencil.lodger
      j (Club.site M cluster ((panel R m u).ratio) j) = (Club.troops M cluster j).center :=
    Cruise.seat pay D R φ capacity E u M cluster p v
  rw [by_offset L O 𝒫 C 𝒜 T M P K (Plateau.Line.patch_here R u) R.B.valid.kernel cluster p r _ near z]
  let cost (d : ℕ) := ∑ b : Site c, ∑' j,
    Poetry.Lantern.gleam ((issue.atoms d arg).leg j) b pins d r z
  have reads := exact_roll issue.ledger arg z pins accepts h
  refine Eq.trans (b:= ↑(Aviary.production (fun j => issue.atoms j arg) p r c z pins)) ?_ reads
  exact congr_arg Complex.ofReal (Fin.sum_univ_eq_sum_range cost (p+1))

/-- The uniform covering bill has at the working period the *actual club's* finite
RG02 coefficient. In particular the position query and Layout used in `Press` are tied to
the independent thermal reset schedule's parameters. -/
theorem finite_binding {g : Bulk.Kernel L C 𝒫 O} (F : Forest ((panel R m u).ratio))
    (t : (panel R m u).Choices) (cluster : Club M) (z : rule (Coarse G) c) (r : ℕ) (h : r ≤ p) :
    let troupe := Club.troops M cluster
    (connectedBill (panel R m u).kernel O 𝒫 C 𝒜 T (fun j => (troupe j).lamp) (fun j => (troupe j).atom)
      (panel R m u).patch (clubOffset L M cluster) p r) c
        (mingle z (Aperture.Bunch.mapC (Club.site M cluster ((panel R m u).ratio)))) =
    ScatterR.history M 𝒜 T g F t (tint G (Exterior.Body 1 c) (exteriorL G c z)) cluster r p := by
  -- change patch by rewriting in lemma using equality BEFORE matching offsets (cast away proof).
  intro troupe
  let ticket := Cruise.ticket pay D R φ capacity E M cluster p v
  let issue := clock.lore x y capacity E ticket
  let stencil := Cruise.rules pay D R φ capacity E u M cluster p v
  let pins := Aperture.Bunch.mapC (Club.site M cluster ((panel R m u).ratio))
  haveI : Nonempty (Card D pay x y E.wants (Burn.horizon E.vac)) := ⟨card⟩
  let arg := Mentor.artifact pay D R φ capacity E ticket stencil card
  haveI : Nonempty (Mentor.Params pay D φ x y E.wants ticket.val.loans E.vac) := ⟨arg⟩
  have eq_means := connectedFK_eq_bill issue.ledger arg (Plateau.Line.patch_here R u)
    R.B.valid.kernel ad g F t (mingle z pins) stencil.cert h
  -- use offset finite version, and cursor
  have near : ∀ j : Club.Keys M cluster, QuadraticLocal.Echo.Sara.seat P L (Plateau.Line.patch_here R u) stencil.lodger
      j (Club.site M cluster ((panel R m u).ratio) j) = (Club.troops M cluster j).center :=
    Cruise.seat pay D R φ capacity E u M cluster p v
  refine Eq.trans (?_ : _ = connectedBill K O 𝒫 C 𝒜 T (fun j => (troupe j).lamp) (fun j => (troupe j).atom)
      P stencil.lodger p r c (mingle z pins)) (eq_means.symm.trans ?_)
  · -- `bill by_offset`
    exact congr_fun (congr_fun (byBill L O 𝒫 C 𝒜 T M P K (Plateau.Line.patch_here R u) R.B.valid.kernel cluster p r _ near) _) _
  let rhs (w : Bulk.Colors (Focus.census (Club.Keys M cluster)) G f) := (Order.observe _ p (Order.logMarked (Bulk.Fk g F t w (tint G (Exterior.Body 1 c) (exteriorL G c z)) p)) r).part (Focus.onto (Finset.univ:Finset (Club.Keys M cluster)))
  exact congr_arg rhs (club_colors L 𝒜 T M P (Plateau.Line.patch_here R u) cluster _ near)
end CP5Bridge
end YM.Integration.FVA1Physical.MixedResets
