import YM.RG11Proof.Horizon.Restrict

/-! Coherence after identification or with nested diagnostic choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Horizon
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal
open scoped Classical BigOperators

variable {J K R I P : Type*} [Field R]
variable (ι : J ↪ K) [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

omit [DecidableEq J] [DecidableEq K] in
/-- Example sufficient conditions on a single horizon pair: grade-complete
injection, preserving unit and signed actions. Does NOT identify two arbitrary
field bases with an injection; those choices are part of the field system.
-/
theorem Coherent.of_position {d : J→ℕ} {e : K→ℕ}
    (he : ∀ j, e (ι j)=d j) (hcap : ∀ i j,e j ≤ d i → j∈Set.range ι) {u v} (hz : ι u = v)
    (H : I→Square K R) (hH : ∀ j,Held ι (H j)) :
    Coherent ι (Constraints.position u d (fun j=> take ι (H j))) (Constraints.position v e H) where
  anchored M i j hj := Constraints.mem_position_iff.mp M.property |>.1 _ _ (by rw [he]; exact lt_of_not_ge (fun h=> hj (hcap _ _ h)))
  legal M := by
    rw [Constraints.mem_position_iff]
    obtain ⟨h1,h2,h3⟩ := Constraints.mem_position_iff.mp M.property
    refine ⟨fun i j t=> h1 _ _ (by simpa [he]),fun j=> ?_,fun i=>?_⟩
    · exact take_apply .. |>.trans (hz.symm ▸ h2 _)
    have hp : Held ι M.val := fun i j t=> h1 _ _ (by rw [he]; exact lt_of_not_ge (fun h=> t (hcap _ _ h)))
    rw [← take_mul _ hp,← take_mul _ (hH i),h3]

namespace Coherent
variable {L : Constraints R J} {V : Constraints R K}

theorem law {c : Change R K} (h : Coherent ι L V) (hc : Law V c) : Law L (restrict ι c) :=
  ⟨hc.1,lawful ι h hc.2⟩

theorem sym_inverse {c : Change R K} (h : Coherent ι L V) (hc : Change.Good V c) :
    restrict ι (c.undo hc)=(restrict ι c).undo (good ι h hc) := by
  refine Change.ext rfl ?_
  let A := subs (reverse c.g hc.ruler) c.Z
  change take ι (squareInv A)=_
  have he : V.Lawful A:= hc.field.subs (reverse_good _ hc.ruler).base
  rw [take_squareInv _ he.baseline (allHeld ι h he)]; rfl

-- No quantitative costs of truncation on growing field horizons addressed.
-- If arrays from two prescriptions restrict coefficientwise at the power
-- horizon, ANY successful calibration at the larger field horizon also
-- solves the smaller one through that power, including its coupling.
variable {shape : P→ℕ} {A B:ArrayAt J R shape} {A' B':ArrayAt K R shape}

omit [DecidableEq J] in
theorem array {c : Change R K} {m n} (hm:m≤n) (h : Coherent ι L V) (hc : Law V c)
    (ha : ArrayThrough m A (slice ι A')) (hb : ArrayThrough m B (slice ι B'))
    (he : ArrayThrough n B' (c.act A')) : ArrayThrough m B ((restrict ι c).act A) := by
  apply hb.trans
  have hx : ArrayThrough m (slice ι B') ((restrict ι c).act (slice ι A')) :=
    slice_action ι (A:=A') (allHeld ι h hc.2) ▸ fun w=> Through.of_le hm (he _)
  exact hx.trans (ha.symm.act hc.1 Change.EquivJet.refl)

theorem solution_down (D : Detector L A) {c : Change R K} {n}
    (h : Coherent ι L V) (hc : Law V c)
    (ha : ArrayThrough n A (slice ι A')) (hb : ArrayThrough n B (slice ι B'))
    (he : ArrayThrough n B' (c.act A')) :
    (restrict ι c).EquivJet (solution D B) n :=
  identification D (law ι h hc) (array ι le_rfl h hc ha hb he)

-- Inverse/conversion usable coherently too; require its tangent hypotheses
-- to actually perform the inverse, as opposed to a mere comparison formal
-- logarithm. This can be used with arbitrary successful D through overlap
-- demands, not just a particular shape detector.
theorem solution_reverse_down (D : Detector L A) {c : Change R K} {n}
    (h : Coherent ι L V) (hc : Change.Good V c) (hs : Change.Good L (solution D B))
    (ha : ArrayThrough n A (slice ι A')) (hb : ArrayThrough n B (slice ι B'))
    (he : ArrayThrough n B' (c.act A')) :
    (restrict ι (c.undo hc)).EquivJet ((solution D B).undo hs) n := by
  rw [sym_inverse _ h hc]
  exact Change.undo_equiv _ _ _ _ (solution_down _ D h ⟨hc.ruler.base,hc.field⟩ ha hb he)
end Coherent
end YM.RG11.Horizon
