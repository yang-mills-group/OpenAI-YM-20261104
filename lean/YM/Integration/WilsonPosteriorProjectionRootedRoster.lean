import YM.Integration.WilsonConditionalTaylorLabels

/-! The prebooked census consists of the *same* finite original Wilson frame
elements as the roster consumed by the realized field invoice. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionRootedRoster

open Lattice Wilson Labels Next.Foundations WilsonConditionalTaylorLabels
open RGComparison.Core16.Spool
open scoped Classical BigOperators

variable {G : Gauge}

def height (e : Entry G) : ℕ := ∑ i : Fin e.1.length, (e.1.get i).1

/-- This is definitionally the original `CoverLabel G (height e)`. -/
def cover (e : Entry G) (i : ↥e.2) : Σ j : Fin (height e+1), ((frames G).level j).Index :=
  ⟨⟨(e.1.get i.val).1, Nat.lt_succ_of_le (Finset.single_le_sum
    (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (e.1.get k).1) (Finset.mem_univ i.val))⟩,
    (e.1.get i.val).2⟩

theorem same (e : Entry G) (i : ↥e.2) :
    investment (sound G (cover e i).1.val) (valuation G (cover e i).1.val) (cover e i).2 =
      packet e i := rfl

end YM.Integration.WilsonPosteriorProjectionRootedRoster
end

