import YM.FormalBulk08.First.Pave
import YM.Comparison.RG02.Symphony.Prima
import YM.RG12.Shadows.Public

/-! The finite-period quadratic comparison on the physical history
returned with a single directed alloy, including fixed-ratio plateaux. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedBoltKinetic
open Function Filter Lattice RG RG.Supply Wilson Precision Exterior Laurent Bloch
open Input Org Extra.Histories Next.Foundations PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open UVExtension Spire Orchard Mast
open FormalBulk08 FormalBulk08.Reef FormalBulk08.Series FormalBulk08.Mesa FormalBulk08.City
open FormalBulk08.Cork FormalBulk08.Flat FormalBulk08.Lotus FormalBulk08.Shore FormalBulk08.Dove
open Comparison.RG02 Comparison.RG02.Symphony PowerSeries
open scoped Classical BigOperators
variable {G : Gauge} {hG : G.Simple} {M : Metals G} {P : Rolls M.p} {A : Alloy M P}
variable {F : Roost.Factor A} (U : Uses F hG) (D : Bolt A)

/-- The finite stationary maps and physical representative of the exact
directed alloy, with the same history at every future period and cutoff. -/
def chain : Bulk.Chain (Issue.trail D) where
  preCosts := M.p
  lengths := P
  post := A.post
  horizon := A.B.M
  O := M.O
  receipt := A.B.ratio
  kin := A.B.kin
  planned := A.B.support
  selected N p m hm := ((D.sticks N p).prices m (Nat.zero_le _) hm).1.path.trans
    (congrArg (fun f => f N m) A.B.bases)
  clips N p m hm := ((D.sticks N p).prices m (Nat.zero_le _) hm).1.clip

/-- Paid on the same actual field and the same pair of adjacent levels. -/
def spare (origin : D.history = U.realBeat 0) : Spare (chain D) where
  currency := M.K
  planned := A.B.plan
  rails := F.pledging.conducts.full
  refund := F.post
  reward N m p hm := by
    change |(D.history N p m).beta - (D.history N p (m+1)).beta -
      A.B.kin.alpha N m| ≤ UVNext.CouplingReset.width A.B.a m F.post
    rw [origin]
    exact (U.housing N p (Spire.Uses.centerP _) m hm).2.1

/-- When an incoming branch has already fixed its Bolt, this uses that
literal witness and the equality certified by its returned arc. -/
def onArc (e : Upland.Arc F U D) : Spare (chain D) := spare U D e.atPeak

/-- With only the directed factor and its registered physical uses, the
native zero branch supplies the Bolt before choosing test indices. -/
theorem available :
    ∃ D' : Bolt A, D'.history = U.realBeat 0 ∧ Graces.Nest F D' ∧ Nonempty (Spare (chain D')) := by
  obtain ⟨D',origin,marked⟩ := U.exists_bolt
  exact ⟨D',origin,marked,⟨spare U D' origin⟩⟩

theorem provenance {C : Family G} (history : C.path = Issue.trail D)
    (stencil : C.params = hol G) (frames : C.labels = Labels.frames G)
    (stamped : HEq C.localSection (localSection G)) : Provenance G C M.O := by
  refine ⟨stencil,frames,stamped,?_⟩
  rw [history]
  exact ⟨A.B.M,A.B.kin,M.p,P,A.post,A.B.support,(chain D).selected,
    fun N p m hm => (D.moves N m p hm).δ⟩

variable {fees : ℕ → ℝ} {majorant : Bid.Worth} {t : ℕ → ℕ}
variable {bank : Legato.Bandage F fees majorant} (world : Cellar U t bank)

/-- The cell built on the original zero branch has exactly the
preselected Bolt's history, as an equality of the whole RG program. -/
theorem yard_history (arc : Upland.Arc F U D) :
    (Cellar.yard (roseA U) world).path = Issue.trail D := by
  change A.B.bake.make (U.realBeat 0) = A.B.bake.make D.history
  exact congrArg (fun history => A.B.bake.make history) arc.atPeak.symm

theorem yard_provenance (arc : Upland.Arc F U D) :
    Provenance G (Cellar.yard (roseA U) world) M.O :=
  provenance D (yard_history U D world arc) rfl rfl HEq.rfl

variable (lodges : ∀ i, Lodge ((A.B.a.clock.op i 0).patch)) (color : G.ColorIndex)

include world in
/-- The complete original degree-zero through degree-two finite tensors
of the chosen physical clip and path at an arbitrary test volume. -/
theorem tensors (arc : Upland.Arc F U D) (N p m : ℕ) (hm : m ≤ N) (s : Side) :
    Through 2 (stone (Dove.model A.B.a lodges (Hay.Wday A.B.a) M.O color N m) s)
      (Hay.novel (D.history N p m).clip (D.history N p m).path s) := by
  have hc := (chain D).clips N p m hm
  change (D.history N p m).clip = (A.B.a.params m).clip at hc
  rw [hc,arc.atPeak]
  exact First.low_use hG (yard_provenance U D world arc) A.B.ratio N p m hm lodges color s

/-- The coefficient is evaluated on the original horizon and the
original loop bank already bought with this directed alloy. -/
theorem calibrated (group : G.Simple) (N m : ℕ) (hm : m<N) :
    coeff 2 (First.stride A.B.a lodges M.O color N m) = A.B.kin.alpha N m :=
  Hay.first_read lodges A.B.ratio group A.B.support N m hm color

theorem physical (origin : D.history = U.realBeat 0) (N p m : ℕ) (hm : m<N) :
    |(D.history N p m).beta - (D.history N p (m+1)).beta -
      coeff 2 (First.stride A.B.a lodges M.O color N m)| ≤
        F.post.radius (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) := by
  rw [calibrated lodges color hG N m hm]
  exact (spare U D origin).reward N m p hm

end YM.Integration.OriginalMarkedBoltKinetic
