import YM.Integration.WilsonPhysicalHistoryGraduateHardTarget
import YM.MergeProof.Tally

/-! Return the original charged hard coefficients to their own support and
inventory on the real installed representation, with the same before-field
all-hit price. The original quiet and singleton modes can be kept or peeled
off on this same registered array. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGroupedHard
open Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open scoped BigOperators Classical

variable {V T : Type*} [DecidableEq V] {Z : Census V} {G : Gauge} {n : Side}
  (P : Rep G n) (o : V → Site n) (H : Hard T P.p P.activities.forced P.activities.K o Z)
  (w : V → ℝ) (pos : ∀ v, 0 < w v) (keep : Finset Z.Mode)

def select (x : Poly Z) : Poly Z :=
  Poly.inject fun s => if s ∈ keep then x.part s else 0

def column (t : T) (i : ℕ) (U : Config G n) : Poly Z :=
  select keep (H.hard t i U)

def grouped (t : T) : Box n → Config G n → Poly Z :=
  tally (barcode P.activities) (column P o H keep t)

include pos in
theorem stored {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a)
    (paid : H.Paid w B a cost) (t : T) :
    Towed w (fun i => (P.activities.forced i).support) (column P o H keep t) B a cost := by
  obtain ⟨cap, protects, funded⟩ := paid.wages
  have summable := (RG3.Letters.Frame.from_hit B a cost (fun i => Poly.price w (cap i))
    (fun i => (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup)
    (fun i => Poly.nonnegative pos (cap i)) expo funded).2.1
  refine ⟨fun i => Poly.price w (cap i), summable, funded, fun i => ?_⟩
  refine ⟨fun s => ‖(cap i).part s‖, fun s => norm_nonneg _, ?_, le_rfl⟩
  intro U s
  by_cases h : s ∈ keep
  · change ‖if s ∈ keep then (H.hard t i U).part s else 0‖ ≤ _
    rw [if_pos h]
    exact ((protects i t U s).1).trans (Complex.re_le_norm _)
  · change ‖if s ∈ keep then (H.hard t i U).part s else 0‖ ≤ _
    rw [if_neg h, norm_zero]
    exact norm_nonneg _

include pos in
theorem original {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a)
    (paid : H.Paid w B a cost) (t : T) :
    Towed w Prod.fst (grouped P o H keep t) B a cost :=
  towing (barcode P.activities) (column P o H keep t)
    (stored P o H w pos keep expo paid t) pos

end YM.Integration.WilsonPhysicalHistoryGroupedHard
end

