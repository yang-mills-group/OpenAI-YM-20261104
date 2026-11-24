import YM.QuadraticLocal.Local.Paying
import YM.AllOrder.Transit.Summit
/-!
# Marked local-comparison geometry, REAL and AUXILIARY

Expose the radii ahead of time. At `t=clock.hatBeta m`, `B=radiusB t`,
all marks participating in a *short* computation here will already have
complete support in a ball at their own (fine) center of this size times 3.

Two **different** cluster radii:
* `survey B`: estimate the omitted REAL Staff groups whose *set of marks
  is spread out* (proof to use core bound `cortex`). This radius also
  lower bounds B, important when estimating the analytic model of those.
* `window B`: match ALL short computations in an engaged group, on the
  appropriately enlarged halo. Eligibility of a Staff word for matching
  will still require `Base ⊆ neighbors window z` of the chosen center --
  no post-pricing smallness on unmatched words inferred from just group size.

There is no restriction that occurrences have different centers even
when requiring disjoint marker slots on a tuple. Reactor masks and
launch prices at coarser epochs are bought separately from these.

Importantly the seam halo `2*Trio.base` is still O_J(B). One may impose
all these conditions in a single post-block delay and size constraint.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Mentor
open Function Filter Lattice Laurent Wilson RG Pressure Extra
open ConnectedActivityE6 PhysicalNext Repeat RemainderComparison
open Deck Push Push.AbsoluteSums
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
namespace Venue -- within Mentor qualify ambiguous QuadraticLocal.Venue? switch
end Venue
namespace Radii
variable (u k s:ℕ) -- Target.halo u
variable (B:ℕ) (hB:1≤B)
local notation "c₀" b:max=> Sleet.cortex u b k s 3
/-- used as `B * factor` near-leg limit -/
def guide (u k s:ℕ):= Sleet.cortex u 1 k s 3 + 5
def survey := guide u k s * B
local notation "Xm"=> (survey u k s B)
lemma first : 5*B≤ survey u k s B:= Nat.mul_le_mul_right B (Nat.le_add_left ..)
include hB
lemma supports : Sleet.cortex u B k s 3 ≤ survey u k s B:= (Sleet.cortex_p hB).trans (Nat.mul_le_mul_right B (Nat.le_add_right ..))
-- `covers_wire` from Messenger for all Charts, with their own occ.radii between B and 3 B.
def sequel (u k s:ℕ):= guide u k s + u + 14
def window := sequel u k s * B
local notation "D"=> window u k s B
omit hB
lemma second : Xm ≤ D:= Nat.mul_le_mul_right B (show guide u k s ≤ guide u k s+u+14 from (by omega))
include hB
lemma suffices_ (r:ℕ)(hr:r ≤3*B): survey u k s B + Mint.width u B r ≤ window u k s B:= by unfold window survey sequel Mint.width; simp_rw [Nat.add_mul]; omega
/-- sufficiently long for all auxiliary proofs -/
def occupancy (u k s:ℕ):= 2*sequel u k s+u+40
-- pay both REAL lower bounds and AUX upper bounds.
local notation "m"=> Trio.base (occupancy u k s) B
local notation "nz"=> Trio.fence (occupancy u k s) B 0
def entitlement := 8*window u k s B+2*Mint.width u B (2*B)+2*Mint.width u B B+16
local notation "r₁"=> entitlement u k s B
omit hB in
lemma space {u k s B:ℕ} {n:Side}(hx: Radii.entitlement u k s B ≤ n.val):
    let r:= Radii.window u k s B
    -- Pose.Shape on whichever follower is small
    2*(r+Mint.width u B (2*B)+3)<n.val ∧ 2*(r+Mint.width u B B)<n.val ∧ 2*(2*r+3)<n.val ∧ 4*r+16≤n.val := by intro r; unfold entitlement at hx; dsimp only [r]; omega -- hB include? inside `omit hB` issue binder explicit
lemma side : let q:=2*window u k s B
             2*q ≤ (Trio.fence (occupancy u k s) B 0).val ∧ q+1 ≤ Trio.base (occupancy u k s) B ∧ entitlement u k s B ≤ (Trio.fence (occupancy u k s) B 0).val ∧ entitlement u k s B ≤ 2*Trio.base (occupancy u k s) B:=by
   intro q; unfold q window;
   unfold entitlement Trio.fence Trio.base Trio.tent Meadow.studio Meadow.roomSize Mint.width occupancy; change 2*_ ≤2*(_+0) ∧ _ ≤ _ ∧ 8*Radii.window u k s B+_+_+16≤ 2*(_+0) ∧ _≤ _; unfold Radii.window; simp only [add_mul,mul_assoc,zero_add]; omega -- Nat.zero Val simpl
-- lower spacing for K at REAL center Halo scheduling. Include gross assumption W.PhBus.Monopoly Lens.
def rentals (u k s:ℕ):= 1+Trio.maxFixed (occupancy u k s)
lemma suffSize {n:Side} (ht: Radii.rentals u k s * B ≤ n.val) : 2*Trio.base (occupancy u k s) B < n.val:= by
    have hv:= Trio.roof (occupancy u k s) B hB; unfold rentals at ht; rw [add_mul, one_mul] at ht; omega
/- marks align once, even if centers aren't inside a BIG chart -/
section placement
variable {V:Type*} (p:V) {c n:Side} (x:Site n)(X:V→Site c)
abbrev warp (p:V)(x:V→ Site c): V→ Cover:= fun i=> Lattice.lift (x i-x p)
local notation "w"=> (warp p X)
variable {u k s B}
omit hB
open Further.PhysicalPeriodLimitF933 Macrame
-- Look.top hidden requires P notation?
lemma own : warp p X p=0:= by rw [warp,sub_self]; simp [Lattice.lift]
variable {U:Type} (x':U)(g:U→Site c)
lemma down (h:c.val∣ n.val)(hE: Macrame.splitter h x=g x')(i:U) : Macrame.splitter h (Aria.Pose.Look.top (warp x' g) x i) = g i := by unfold Aria.Pose.Look.top; rw [map_add, Macrame.branch, hE,warp,wrap_lift,sub_add_cancel]
lemma midpoint (V':Site n): Aria.Pose.Look.top (warp x' g) V' x'= V':= by rw [Aria.Pose.Look.top,Radii.own,map_zero,zero_add]
-- matching field times geometry at ANY BIG topology
lemma top_inner (i:U) (hv: separation (g x') (g i) ≤ survey u k s B): separation x (Aria.Pose.Look.top (warp x' g) x i) ≤ survey u k s B:= by
    exact Slide.sep _ _ (Work.E08.lift_mem_box hv)
end placement
end Radii
end YM.QuadraticLocal.Mentor
