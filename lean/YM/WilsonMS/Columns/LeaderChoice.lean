import YM.WilsonMS.Columns.LoopTeam
/-! # Parity can be imposed when constructing the comparison

Not saying generic supplied `Prescription` has this property. Probe the
actual high-mode matching, in particular the freedom in `Move`. Restrict
moves to the rank-bearing Taylor positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.LoopRank.Leader
open MS Function Filter Finset Set MeasureTheory Real
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Frame Wire Color Detect Native
  Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal
open LogTime Domain Local.Physical High Knobs Wind Menus
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {h u : ℤ} {b : Bool} {d k r : ℕ}

lemma rank_torch {P : Detect.Law G} (he : pays k P) (l : List (Lane4 G)) (hh : ¬Allows k l.length)
    (j : ℕ) : torch j P l = 0 := by
  unfold torch
  rw [show fieldVal P (ray l) = (0 : ℝ → ℂ) from funext fun x => he (sail _ x) (by simpa using hh)]
  simp [stage, Tensor.diagonal, Tensor.coeff]

lemma rank_absent {P Z : Reading G} (h : ∀ i, pays k (P i)) (hp : ∀ i, pays k (Z i))
    (hv : ¬Allows k r) : slice (P - Z) b r u = 0 := by
  ext1 y
  funext w
  unfold slice
  split
  rename_i ht
  swap
  rfl
  have H (t : ℝ) : skin wfield u ((P - Z) (y, t)) w = 0 := by
    unfold skin
    split
    swap
    rfl
    have he (i) : pays k ((P - Z) i) := fun w hw => by
      rw [Pi.sub_apply, Pi.sub_apply, h i w hw, hp i w hw, sub_self]
    exact rank_torch (he _) w (ht.2 ▸ hv) _
  exact
    Tendsto.limUnder_eq
      (funext H ▸
        (show Tendsto (fun _ : ℝ => (0 : ℂ)) atTop _ from tendsto_const_nhds (x := (0 : ℂ))))

abbrev Key0 (k : ℕ) :=
  { p : Plan // Modal k p }

instance (k : ℕ) : Inhabited (Key0 k) :=
  ⟨⟨⟨0, 0, 0⟩, ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩⟩⟩

def pureTeam (X : Code Key0) : Team := fun i => (X i).val

def K0 (G : Gauge) : Knobs Key0 G
    where
  wake X := (Key G).wake (pureTeam X)
  stay _ _ _ h := (Key G).stay _ _ _ (fun i hi => congr_arg Subtype.val (h i hi))

lemma Wound (P : Code Key0) {Q : Team} {X : ℝ → Law G} (he : Valid Q)
    (hp : Career G (pureTeam P) Q k r h X) (ht : 1 ≤ k) : ∃ Z, Move true (K0 G) P Z k r h X := by
  let Z : Code Key0 := fun i => ⟨Q i, he i⟩
  exact
    ⟨Z,
      rewind (K := K0 G) rfl rfl (fun i hi => Subtype.ext (hp.past i hi))
        (fun x => ((skyPC G _).owes k |>.stay x).joint)
        (fun x => ((skyPC G Q).owes k |>.stay x).joint) (bulk_pay (skyPC G _) (skyPC G Q) hp ht)⟩

lemma scales_pair (P : Code Key0) (Hp : Allows k 0) {p q : ℝ → ℝ} (h : 1 ≤ k) (hp : Ready p)
    (hq : Ready q) : ∃ Q, Move true (K0 G) P Q k 2 4 (fun i => ranktwo (p i) (q i)) := by
  obtain ⟨u, rfl⟩ := hp.scalar
  obtain ⟨v, rfl⟩ := hq.scalar
  let t : Polynomial ℝ := Polynomial.C (2 : ℝ)⁻¹ * u
  let s := t + v
  let Q := rush (pureTeam P) t s k
  have hz : Valid Q := by
    intro i
    by_cases he : i = k
    · subst i
      rw [show Q k = _ from if_pos (Eq.refl k)]
      exact ⟨fun hx => (hx Hp).elim, (P k).property.shift⟩
    rw [show Q i = pureTeam P i from if_neg he]
    exact (P i).property
  apply Wound P hz _ h
  convert! scale_car (G := G) (pureTeam P) t s h using 2
  ext i
  simp [s, t]

lemma scales_cube (P : Code Key0) (H : G.Simple) (Hx : 1 < k) (ht : Allows k 1) {F : ℝ → ℝ}
    (h : Ready F) : ∃ Q, Move true (K0 G) P Q k 3 4 (fun i => (F i : ℂ) • LE G 4) := by
  let p := pureTeam P
  obtain ⟨R, rfl⟩ := h.scalar
  let q : Team := fun i =>
    { p i with coupling := if i = k then (p i).coupling - R else (p i).coupling }
  have he i (hi : i ≠ k) : p i = q i := by simp [q, hi]
  have hv x : style G p x k - style G q x k = (↑(R.eval x) : ℂ) • core G 1 := by
    rw [style_diff x (fun i hi => he i (ne_of_lt hi)) (by omega),
      ferryPlan x (p := p) (q := q) (fun _ => rfl) (fun _ => rfl), sub_self, add_zero]
    congr 1
    simp [q, shift, Nat.ne_of_gt Hx, show k ≠ 0 from (by omega)]
  apply Wound P (Q := q) _ _ Hx.le
  · intro i
    by_cases h : i = k
    swap
    · rw [← he i h]
      exact (P i).property
    subst i
    exact ⟨fun x => (P k).property.wave x, fun hg => (hg ht).elim⟩
  exact
    ⟨fun i hi => he i (ne_of_lt hi),
      (fun x => by
        rw [hv]
        exact Limit.smul _ (participates G 1)),
      fun x => by
      rw [hv]
      exact Lifting.Fits.smul _ (bulk_three H)⟩

open Land Motif Halo Dock Emit Outlook
variable {B : Deck G} {A : Booked B} (X : MS_Data G A)

theorem oddWaves (H : G.Simple) :
    ∃ Q : Team, Valid Q ∧ Fixed (col (skyline G Q)) (Archive 4 X.bulk) true 4 1 := by
  let R := Archive 4 X.bulk
  let L : Tuning (Key G) R (Menus.LE G 4) := action_seek H (stable X.bulkOK)
  let k := K0 G
  obtain hD := dock X.bulkOK wisdom
  have hP (p : Code Key0) : Spheres wave (spaceL G) (k.wake p) (k.wake p) ((2 : ℂ)⁻¹) 1 true :=
    L.commute _
  suffices hx : ∃ P : Code Key0, Fixed (k.wake P) R true 4 1 from
    by
    obtain ⟨p, hp⟩ := hx
    exact ⟨pureTeam p, fun n => (p n).property, hp⟩
  refine
    assigned hP hD.master hD.good (fun _ => L.rates _) hD.open' ?_ (by norm_num) ?_ (fun _ => default)
  · intro X n hn hp i hi s
    rw [paths, Finset.mem_Ico] at hi
    exact hp _ (by omega) (by omega) _ (fun _ => Nat.succ_pos _)
  intro n hn r hr u hu hux Z EE HE
  let M := k.wake Z n - R n
  let V := slice M true r u
  by_cases hN : Allows (n + 2) r
  swap
  · refine ⟨Z, Move.refl V ?_⟩
    intro i w _ hw
    rw [show V = 0 from
        rank_absent (P := k.wake Z n)
          (fun i => Pc_b i.1 (skyPC G _) (fun a => (Z a).property) n (exp i.2)) (action_archive X n)
          hN]
    rfl
  have hz := advanced (hP Z) hD.master hn hr EE
  have hp : Ready V := slice_ready hz hux (Ready.sub ((hP Z).poly n) (hD.master.poly n))
  have hv (i : ℝ) : Class (V i) u :=
    { solid := slice_solid hz hux fun t => ((hP Z).trueC n t).sub (hD.master.trueC n t)
      graded := slice_form hz hux
      signed :=
        slice_signed hz hux fun t =>
          SignedScope.sub ((hP Z).reflects n t rfl) (hD.master.reflects n t rfl)
      closed := fun w hw => closes (hP Z) hD.master hD.good hn hr EE hux HE i w (fun _ => hw) }
  have h0 : 0 < r := hr rfl
  rcases lt_or_eq_of_le hux with h1 | h1
  exact ⟨Z, Move.refl V fun i w hw hp => lower_at H h1 (hv i) (hw rfl) (by omega)⟩
  subst u
  rcases lt_or_ge r 4 with h1 | h1
  swap
  · exact ⟨Z, Move.refl V (fun i w hw hx => large_class (hv i) (le_refl 4) r h1 w (hw rfl) hx)⟩
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 from by omega) with hr1 | hr1 | hr1 <;> subst r
  · refine ⟨Z, Move.refl V ?_⟩
    intro i w hw h
    obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp h
    exact (hv i).single H j (hw rfl)
  · obtain ⟨p, q, hp, hq, H⟩ := pair_inter H hp hv
    obtain ⟨W, hZ⟩ := scales_pair (G := G) Z (Allows.linear hN) hn hp hq
    exact ⟨W, hZ.replace fun i w hw hx => H i w (hw rfl) hx⟩
  obtain ⟨w, hw, hC, hx⟩ := L.stamp
  rcases eq_or_ne n 1 with he | he
  · subst n
    exact
      ⟨Z,
        Move.refl V
          (fun i w hw h =>
            zero_triple_born (le_refl 4) (hP Z) R hD.master (L.leads (pureTeam Z)) i w (hw rfl) h)⟩
  obtain ⟨p, hp, he'⟩ := cube_inter H hC hw hx hp hv
  obtain ⟨W, hZ⟩ := scales_cube Z H (k := n) (by omega) (Allows.linear hN) hp
  exact ⟨W, hZ.replace fun i w hw h => he' i w (hw rfl) h⟩
end YM.WilsonMS.LoopRank.Leader
