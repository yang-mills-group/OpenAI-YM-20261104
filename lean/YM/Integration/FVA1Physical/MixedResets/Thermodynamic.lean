import YM.AllOrder.Ink.Pump

/-!
# Normalization for the cover prescription

The comparison coefficients here will be **cover** coefficients,
periodized on the working torus. In particular *not* obtained by taking a large-volume
limit of actual RG outputs. `onCover` acts on a bill of FORMAL (jet) polynomials.
Its arguments can include source pins as well as field pins. Repeat all of them
periodically. We will apply this to CONNECTED bills, once per disjoint group of
analytic input rows, and to the vacuum action, not to product moments.

This pins even numbers/profiles evaluated on a **fixed finite** working torus.
No consistency requirement on finite-torus bills, which can have winding error.
This lemma is the exact extraction step: exponential accuracy on all auxiliary
periods + the supplier's Laurent representation ⇒ the published packet (at ANY
admitted working modulus, including all its winding terms) realizes precisely these
independent coefficients. At this layer the packet is in its ordinary field table
form; use the generated curvature packets to compare in representation norm.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.MixedResets
open Filter Function Lattice AllOrder AllOrder.Fire AllOrder.Ker AllOrder.Ink
open AllOrder.Ink.Money Further.PhysicalPeriodLimitF933 Shingle
open scoped Topology Classical

variable {X : Type} [Fintype X] {n : Side}

/-- One (finite) Bill, usually from Wick calculus with color & marker pins `X`. -/
abbrev ComplexBill (X : Type) := (n : Side) → rule X n → ℂ

/-- Evaluate a tile-window (pull back every field and marker argument), dividing by tile count. -/
def tileAt (bill : ComplexBill X) {N : Side} {tiles : ℕ}
    (w : Macrame.Window n N tiles) (z : rule X n) : ℂ :=
  ((tiles : ℝ)⁻¹) • bill N (convey w z)

def inTiles (bill : ComplexBill X) (z : rule X n) (t : ℕ) : ℂ :=
  tileAt bill (Ink.Echo.arm n t) z

/-- The cover value. Extension by zero outside the class with proved thermodynamic limits. -/
def onCover (bill : ComplexBill X) (z : rule X n) : ℂ :=
  if h : ∃ x, Tendsto (inTiles bill z) atTop (𝓝 x) then Classical.choose h else 0

omit [Fintype X] in
lemma onCover_eq {b : ComplexBill X} {z : rule X n} {x : ℂ}
    (h : Tendsto (inTiles b z) atTop (𝓝 x)) : onCover b z = x := by
  rw [onCover, dif_pos (Exists.intro x h)]
  exact tendsto_nhds_unique (Classical.choose_spec (show ∃ x, Tendsto (inTiles b z) atTop (𝓝 x) from ⟨x, h⟩)) h

variable {Ad : Side → Prop} {k : ℕ} {a C : ℝ} {e : Side → ℝ} {fb : Bills X}
  {published : Ink.Field X} {bill : ComplexBill X}

/-- Arbitrary test modulus and window sequence. Use a *different*, finite Wick bill `bill`
matching the polynomial `fb` on all admitted lattice sizes. The latter has been exponentially
compared with the tile-additive bill from the Laurent analysis (`Pert`). -/
theorem cover_tendsto {S : ℕ → Side} {T : ℕ → ℕ}
    (w : ∀ i, Macrame.Window n (S i) (T i))
    (hS : Tendsto (fun i => (S i).val) atTop atTop) (hT : ∀ i, 0 < T i)
    (wrap : Pert Ad fb published a C e k) (pulse : Echo.Pulsed e)
    (ha : 0 < a) (hA : Often Ad) (identifies : ∀ m : Side, Ad m → bill m = ((↑) ∘ (fb m)))
    (z : rule X n) :
    Tendsto (fun i => tileAt bill (w i) z) atTop (𝓝 (published.table n z : ℂ)) := by
  have hlim := Ink.Echo.transported w wrap pulse hS ha hA hT _ (LinTest.eval _ z)
  refine ((Complex.continuous_ofReal.tendsto _).comp hlim).congr' ?_
  obtain ⟨d, hd⟩ := hA
  filter_upwards [hS.eventually (eventually_ge_atTop d)] with i hi
  change ((↑(((T i : ℝ)⁻¹) * fb (S i) (convey (w i) z))) : ℂ) = tileAt bill (w i) z -- defeq function space smul
  rw [tileAt, identifies _ (hd _ hi), Function.comp_apply]
  simp [Complex.real_smul]

theorem published_eq_cover
    (h : Pert Ad fb published a C e k) (pulse : Echo.Pulsed e)
    (ha : 0 < a) (hA : Often Ad) (identifies : ∀ m : Side, Ad m → bill m = ((↑) ∘ (fb m)))
    (z : rule X n) : (published.table n z : ℂ) = onCover bill z := by
  symm
  exact onCover_eq (cover_tendsto (Ink.Echo.arm n) (Ink.Echo.limitless n) (fun i => by positivity) h pulse ha hA identifies z)

end YM.Integration.FVA1Physical.MixedResets
