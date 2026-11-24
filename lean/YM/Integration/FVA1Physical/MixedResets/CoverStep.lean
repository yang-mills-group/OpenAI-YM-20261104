import YM.Integration.FVA1Physical.MixedResets.CoverRoll
import YM.QuadraticLocal.Fk.Unit
import YM.QuadraticLocal.Earn.Blend

/-!
# Whole marked analytical input and Wilson cover step

Extensional kernel prescription *on the given render of the input* (complete action step on the
same layout as `coverAction`). Elementary superposition exactly as for `Bulk.Fk`, with its
exponential/log conventions. Term at each club is its FULL connected coefficient on the COVER,
charge signs/complex source probes afterwards. Sum on that mixed subset including all actual
addresses, no dropping repeated geometrical positions or forming an absolute majorant as forecast.
When an incoming log generator itself is already mixed it acts in the club as one generator.
Separate sums for global field-independent inputs (exact passthrough). Consume at purchases
supplying convergence and exponential licenses.
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
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn
open scoped Classical Topology BigOperators

variable {c f : Side} (S : StepData c f) {G : Gauge} (O : ChartRatio G)
  (action : PathData G) (clip : Clip) (U : Layout G) (extra : Finset Age)
  {V : Type} [Fintype V] [DecidableEq V] {I : Marker.Census V}
  {ι α : Type} {passport : Passport f V}
  (M : ι → Row passport I G α)
set_option quotPrecheck false

def clubOffset (u : Club M) (j : Club.Keys M u) : Site S.patch.L :=
  S.ratio.residue (Club.troops M u j).center

/-- Normalized (no marker weights/test yet), exact mixed coefficient including all action vertices,
summed using the COVER convention. -/
def clubCoefficient (u : Club M) (p r : ℕ) (z : rule (Coarse G) c) : ℂ :=
  coverImpulse (P := S.patch) S.kernel O action clip U extra
    (fun j : Club.Keys M u => (Club.troops M u j).lamp)
    (fun j : Club.Keys M u => (Club.troops M u j).atom)
    (clubOffset S M u) p r (Aperture.Bunch.mapC (Club.site M u S.ratio)) z

def clubOutput (p r : ℕ) (t : α) (z : rule (Coarse G) c) (u : Club M) : Poly I :=
  Poly.send (Club.alliance M u) (clubCoefficient S O action clip U extra M u p r z *
    ∏ i ∈ u.val, (M i).paint t)

def globalOutput (r : ℕ) (t : α) (j : Solo.Watching M) : Poly I :=
  let L := M j.val
  Poly.send L.mode (L.paint t * (↑(L.markReceipt r 0) : ℂ))

/-- Only evaluated/formal coefficients (before coupling reset). `CoverModel` will supply
analytic rows rendering this prescription from their own exponential budgets. -/
def coverStep (p r : ℕ) (t : α) (z : rule (Coarse G) c) : Poly I :=
  (∑' u : Club M, clubOutput S O action clip U extra M p r t z u) +
    (∑' i : Solo.Watching M, globalOutput M r t i)

open QuadraticLocal.Echo
variable (P : Patch) (K : KernelChoices) (hP : S.patch = P) (hK : S.kernel = K)
  (u : Club M) (p r : ℕ)
local notation "X" => Club.Keys M u
local notation "b" => fun j : Club.Keys M u => (Club.troops M u j).lamp
local notation "atms" => fun j : Club.Keys M u => (Club.troops M u j).atom
local notation "pins" => Aperture.Bunch.mapC (Club.site M u S.ratio)

include hK
omit [Fintype V]
/-- Use a different presentation of the step parameters. Useful at the time cost is paid. -/
lemma by_offset (off : Club.Keys M u → Site P.L)
    (loc : ∀ j : Club.Keys M u,
      Sara.seat P S hP off j (Club.site M u S.ratio j) = (Club.troops M u j).center)
    (z : rule (Coarse G) c) :
    clubCoefficient S O action clip U extra M u p r z =
      coverImpulse (P := P) K O action clip U extra b atms off p r pins z := by
  subst P K
  unfold clubCoefficient
  rw [show off = clubOffset S M u from ?_]
  funext j
  exact (S.ratio.assemble_res (Club.site M u S.ratio j, off j)).symm.trans
    (congr_arg S.ratio.residue (loc j))

omit hK
/-- Thus `Balcony.displayC` used on a tiling bills the true row profiles.
On the working torus, exactly the unmutilated club of rows. -/
theorem club_colors (off : Club.Keys M u → Site P.L)
    (loc : ∀ j : Club.Keys M u, Sara.seat P S hP off j (Club.site M u S.ratio j) = (Club.troops M u j).center) :
    Balcony.displayC b atms (Sara.seat P S hP off) U extra pins = ScatterR.birth M U extra u := by
  exact ScatterR.cursor (Club.troops M u) U extra _ Focus.detailI 1
    (fun j : Club.Keys M u => (Club.troops M u j).lamp.toll) (Club.site M u S.ratio) _ loc

end YM.Integration.FVA1Physical.MixedResets
