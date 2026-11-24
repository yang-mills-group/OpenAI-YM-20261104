import YM.Integration.MSFeeCoordinates

/-! Change of marked prescription inside the original finite Wilson
perturbative functional, at each regulator and every perturbative order. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace YM.Integration.MSFeeReadout

open Finset Function FVA2 Lattice MS MS.Local.Physical MS.Land MS.Menus MSFeeCoordinates
open MS.Book.Program
open scoped Classical BigOperators

variable {G : Gauge} {B : Deck G} {I : Type} [LinearOrder I]
variable (V : Warehouse G) (q : Side) (d : I → ℕ) (t : Team) (x : ℝ)
variable (o : Cover) (c : I → Cover) (s : Finset I)

abbrev Slots (B : Deck G) (d : I → ℕ) (s : Finset I) := (i : s) → Glyph B (d i.val)
abbrev Values (B : Deck G) (d : I → ℕ) (s : Finset I) :=
  (i : s) → Glyph B (d i.val) → PowerSeries ℝ

def splitCrew : Track.Crew V B d s ≃
    (p : Slots B d s) × ((i : s) → V.Atom (p i).size) where
  toFun u := ⟨fun i => (u i).1, fun i => (u i).2⟩
  invFun g i := ⟨g.1 i, g.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl

def bare (p : Slots B d s) : PowerSeries ℝ :=
  ∑ b : (i : s) → V.Atom (p i).size,
    (∏ i : s, PowerSeries.C (V.prices B (p i).size (p i).grade (p i).2.2 (b i))) *
      Track.deckRead V q d t x o c s (fun i => ⟨p i, b i⟩)

def contract (Z : Values B d s) : PowerSeries ℝ :=
  ∑ p : Slots B d s, (∏ i : s, Z i (p i)) * bare V q d t x o c s p

theorem ticket (Z : (i : I) → Acts B (d i)) :
    Track.ticketRead V q d t x Z o c s =
      contract V q d t x o c s (fun i j => Channel.credits j x (Z i.val)) := by
  classical
  unfold Track.ticketRead
  rw [← (Equiv.sum_comp (splitCrew (B := B) V d s).symm
    (fun u => Track.debt V d Z x s u * Track.deckRead V q d t x o c s u)),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [bare, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (∏ i : s, Channel.credits (p i) x (Z i.val) *
    PowerSeries.C (V.prices B (p i).size (p i).grade (p i).2.2 (b i))) * _ = _
  rw [Finset.prod_mul_distrib, mul_assoc]
  rfl

theorem bare_extend (e : I → ℕ) (l : ∀ i, e i ≤ d i) (p : Slots B e s) :
    bare V q d t x o c s (fun i => extend (l i.val) (p i)) =
      bare V q e t x o c s p := rfl

def fits (e : I → ℕ) (p : Slots B d s) := ∀ i : s, (p i).size ≤ e i.val

def subslots (e : I → ℕ) (l : ∀ i, e i ≤ d i) :
    Slots B e s ≃ {p : Slots B d s // fits d s e p} where
  toFun p := ⟨fun i => extend (l i.val) (p i), fun i => remaining (p i)⟩
  invFun p := fun i => restrict (p.val i) (p.property i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem contraction_lift (e : I → ℕ) (l : ∀ i, e i ≤ d i) (Z : (i : I) → Acts B (e i)) :
    contract V q d t x o c s (fun i j => evaluate x (packet (l i.val) (Z i.val) j)) =
      Track.ticketRead V q e t x Z o c s := by
  classical
  rw [ticket]
  let f (p : Slots B d s) :=
    (∏ i : s, evaluate x (packet (l i.val) (Z i.val) (p i))) * bare V q d t x o c s p
  have off (p : Slots B d s) (a : ¬ fits d s e p) : f p = 0 := by
    obtain ⟨i, hi⟩ := not_forall.mp a
    have zero : evaluate x (packet (l i.val) (Z i.val) (p i)) = 0 := by
      rw [packet, dif_neg hi, map_zero]
    change (∏ j : s, evaluate x (packet (l j.val) (Z j.val) (p j))) *
      bare V q d t x o c s p = 0
    have hn : (∏ j : s, evaluate x (packet (l j.val) (Z j.val) (p j))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) zero
    rw [hn, zero_mul]
  have trace : (∑ p : Slots B d s, f p) = ∑ p : {p : Slots B d s // fits d s e p}, f p.val := by
    rw [← Finset.sum_subtype (p := fits d s e)
      ((Finset.univ : Finset (Slots B d s)).filter (fits d s e)) (fun p => by simp) f]
    apply (Finset.sum_subset (Finset.filter_subset ..) ?_).symm
    intro p _ hp
    exact off p (by simpa using hp)
  change (∑ p : Slots B d s, f p) = _
  rw [trace, ← (Equiv.sum_comp (subslots (B := B) d s e l) (fun p => f p.val))]
  apply Finset.sum_congr rfl
  intro p _
  change (∏ i : s, evaluate x (packet (l i.val) (Z i.val) (extend (l i.val) (p i)))) *
      bare V q d t x o c s (fun i => extend (l i.val) (p i)) = _
  simp only [packet_extend, evaluated, bare_extend]

theorem multilinear {J : s → Type} [∀ i, Fintype (J i)]
    (w : (i : s) → J i → PowerSeries ℝ)
    (u : (i : s) → J i → Glyph B (d i.val) → PowerSeries ℝ) :
    contract V q d t x o c s (fun i j => ∑ a, w i a * u i a j) =
      ∑ a : (i : s) → J i, (∏ i : s, w i (a i)) *
        contract V q d t x o c s (fun i => u i (a i)) := by
  classical
  unfold contract
  simp_rw [Fintype.prod_sum, Finset.sum_mul, Finset.prod_mul_distrib, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm]

variable [Fintype I]

def dimensions (a : Slots B d Finset.univ) (i : I) := (a ⟨i, Finset.mem_univ i⟩).size

def originalFees (P : Prescription B) (a : Slots B d Finset.univ) (i : I) :
    Acts B (dimensions d a i) :=
  P.fees (dimensions d a i) (a ⟨i, Finset.mem_univ i⟩).2

theorem whole (P : Prescription B) (Z : (i : I) → Acts B (d i)) :
    Track.ticketRead V q d P.team x Z o c Finset.univ =
      ∑ a : Slots B d Finset.univ,
        (∏ i : (Finset.univ : Finset I), evaluate x (receiver P (Z i.val) (a i))) *
          Track.ticketRead V q (dimensions d a) P.team x (originalFees d P a) o c Finset.univ := by
  classical
  rw [ticket]
  simp_rw [← original P]
  rw [multilinear]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact contraction_lift V q d P.team x o c Finset.univ (dimensions d a)
    (fun i => remaining (a ⟨i, Finset.mem_univ i⟩)) (originalFees d P a)

end YM.Integration.MSFeeReadout
