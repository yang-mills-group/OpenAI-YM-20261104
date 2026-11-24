import YM.QuadraticLocal.Lamps
import YM.MergeProof.Tally

/-! Collect the genuine signed old regular entries by their true support,
with a selected family of original rows. The selection can keep the scalar
clear entries separate from those conditioned on the local healthy mask. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGroupedLamps
open Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open scoped BigOperators Classical

variable {V T I : Type*} [DecidableEq V] {Z : Census V} {G : Gauge} {n : Side}
  {p : BudgetPoint} {o : V → Site n} (L : Lamps T I G p o Z)
  (w : V → ℝ) (pos : ∀ v, 0 < w v) (entries : Set I)

def row (t : T) (i : I) (U : Config G n) : Poly Z := if i ∈ entries then L.frame i t U else 0

def grouped (t : T) : Support n → Config G n → Poly Z := tally L.ground (row L entries t)

include pos in
theorem stored {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : L.Paid w B a cost) (t : T) :
    Towed w L.ground (row L entries t) B a cost := by
  obtain ⟨cap, positive, protects, funded⟩ := paid.budget
  let fees (i : I) := Poly.toll w (L.mode i)*cap i
  have bound (i : I) := protects i t (L.address i).site (L.address i).anchor
  have summable := (RG3.Letters.Frame.from_hit B a cost fees
    (fun i => ⟨(L.address i).site, (L.address i).anchor⟩)
    (fun i => mul_nonneg (Poly.worth pos (L.mode i)).le (positive i)) expo funded).2.1
  refine ⟨fees, summable, funded, fun i => ?_⟩
  let receipt (s : Z.Mode) : ℝ := if s=L.mode i then cap i else 0
  refine ⟨receipt, fun s => ?_, ?_, ?_⟩
  · by_cases same : s=L.mode i <;> simp [receipt, same, positive]
  · intro U s
    by_cases same : s = L.mode i
    · subst s
      by_cases belongs : i ∈ entries
      · simpa [row, belongs, Lamps.frame, Poly.part_send, receipt] using L.light_size i t U (bound i)
      · simp [row, belongs, receipt, positive]
    · by_cases belongs : i ∈ entries <;> simp [row, belongs, Lamps.frame, Poly.part_send, same, receipt]
  · simp [wordsPrice, receipt, fees]

include pos in
theorem original {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : L.Paid w B a cost) (t : T) :
    Towed w id (grouped L entries t) B a cost :=
  towing L.ground (row L entries t) (stored L w pos entries expo paid t) pos

end YM.Integration.WilsonPhysicalHistoryGroupedLamps
end
