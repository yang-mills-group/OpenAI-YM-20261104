import YM.Integration.ActualRunSpring
import YM.Push.STATIONARY_UNIFORM.Continue

/-!
An actual stationary service for the original Spring forest, with explicit
germ compatibility to the stationary map already retained by the Run.
The numerical quote is selected from the Run, step and requested order before
the cutoff, period or inserted field.  The service branch is auxiliary: the
original stationary map is retained and related only by the proved local
equality.  No global branch equality or physical-field radius payment follows.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualSpringStationaryService

open Filter Lattice Wilson RG Precision Tree
open PhysicalNext.Repeat.Legato
open scoped Classical Topology

variable {G : Gauge}

def quotes (R : Run G) (m n : ℕ) :
    Push.Uniform.Before G
      (R.alloy.B.a.params (m + 1)).width
      (R.alloy.B.a.params (m + 1)).paths
      (R.alloy.B.a.clock.J (m + 1)) R.alloy.B.a.clock.kernel (n + 3) :=
  Classical.choice (Push.Uniform.pre_order G _ _ _ _ (by omega))

structure Refinement {R : Run G} {N p m : ℕ} {hm : m < N}
    (P : ActualRunSpring.Packet R N p m hm) (n : ℕ) where
  station : Bid.Dir G (R.alloy.B.a.S.side m p) → AxisChart G P.spring.O
  service : (quotes R m n).Service P.spring.O
    (R.alloy.B.a.params (m + 1)).clip
    (R.alloy.B.kin.path N (m + 1)) station
  original_germ :
    R.alloy.B.kin.stationary N m p P.spring.O =ᶠ[𝓝 0] station

theorem refinement_exists {R : Run G} {N p m : ℕ} {hm : m < N}
    (P : ActualRunSpring.Packet R N p m hm) (n : ℕ) :
    Nonempty (Refinement P n) := by
  have hL : Bid.Larger (G := G) (R.alloy.B.a.clock.op m p) :=
    (P.spring.H.houses P.point).laws.data.room.larger
  obtain ⟨g, hg⟩ := (quotes R m n).graph P.spring.O
    (R.alloy.B.support.cap N (m + 1) hm) hL rfl rfl
  exact ⟨⟨g, hg, hg.is_extension
    ((R.alloy.B.support.critical N m p hm P.spring.O).1)⟩⟩

def selected {R : Run G} {N p m : ℕ} {hm : m < N}
    (P : ActualRunSpring.Packet R N p m hm) (n : ℕ) : Refinement P n :=
  Classical.choice (refinement_exists P n)

theorem original_germ {R : Run G} {N p m : ℕ} {hm : m < N}
    (P : ActualRunSpring.Packet R N p m hm) (n : ℕ) :
    R.alloy.B.kin.stationary N m p P.spring.O =ᶠ[𝓝 0]
      (selected P n).station :=
  (selected P n).original_germ

end YM.Integration.ActualSpringStationaryService
