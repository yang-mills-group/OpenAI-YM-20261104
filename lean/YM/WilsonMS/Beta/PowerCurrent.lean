import YM.WilsonMS.Beta.StyleScale
/-!
# Variation in the scale parameter at *finite R*

Extract the actually varied pieces that survive later, from the native
high-mode Wilsonian kernels after any finite station. Keep net course
rules since the input authorizations are literal on the conserved symbols.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS
open Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native Native.Wilsonian
  Paint
open Book Convolve City Logarithm Program Signal
open Cylinder Lab Menus Lifting Landau.Detect.Mark Wind
open PowerSeries (coeff)
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {X : Dec G} {T : Team} (h : Valid T) (hp : PC G T X)
variable (x y t : ℝ)

private lemma cycle_eq {s t : Wind.Flow G} (ht : TouchF s) (hf : TouchF t) (i : ℝ)
    (w : List (Lane4 G)) (hx : ∀ k : List (Lane4 G), k.length = w.length + 2 → s i k = t i k) :
    Wiref G s i w = Wiref G t i w := by
  change orbit (Cpu G i) μzone (s i) w = orbit (Cpu G i) μzone (t i) w
  rw [finite_cc μzone (period0 μzone cour0 (main_f _) ht),
    finite_cc μzone (period0 μzone cour0 (main_f _) hf)]
  unfold Ccy
  simp only [at_trc]
  simp_rw [hx (_ :: _ :: w) rfl]

private lemma tree_top_eq {A V H Z : Law G} {a b c : ℕ} (h : a + b = c + 2) (ha : pays a A)
    (hb : pays b V) (he : pays a H) (ht : pays b Z)
    (hV : ∀ i : Legs (Lane4 G), i.length = a → A i = H i)
    (hZ : ∀ i : Legs (Lane4 G), i.length = b → V i = Z i) (P : Flux (BH G) QP ℂ) (w : Legs (Lane4 G))
    (hw : w.length = c) : tree parity P A V w = tree parity P H Z w := by
  refine scatter_congr _ _ _ _ (fun l r hd => ?_)
  unfold attaches
  obtain hz := split_length hd
  dsimp only
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy (l.length + 1) a with hL | hL | hL
  · have ht' : ¬Allows b (r.length + 1) := fun k =>
      Nat.not_le.mpr (by omega : b < r.length + 1) k.smaller
    rw [hb (_ :: r) ht', ht (_ :: r) ht', hb (_ :: r) ht', ht (_ :: r) ht']
    ring
  · rw [hV (_ :: l) hL, hV (_ :: l) hL,
      hZ (_ :: r)
        (by
          simp only [List.length_cons]
          omega),
      hZ (_ :: r)
        (by
          simp only [List.length_cons]
          omega)]
  have hu : ¬Allows a (l.length + 1) := fun k => Nat.not_le.mpr hL k.smaller
  rw [ha (_ :: l) hu, ha (_ :: l) hu, he (_ :: l) hu, he (_ :: l) hu]
  ring
include h hp

private lemma vacant (i : ℕ) (w : List (Lane4 G)) (hw : i + 2 < w.length) : X i x t w = 0 :=
  Pc_b x hp h i t w (fun k => Nat.not_le_of_lt hw k.smaller)

private lemma equal_full_one : X 1 x = X 1 y := by
  obtain hs := hp.recu 1 Nat.one_pos x
  obtain hf := hp.recu 1 Nat.one_pos y
  unfold Wind.path at hs hf
  rw [show Domain.paths (1 : ℕ) 1 = ∅ from Finset.Ico_self 1, Finset.sum_empty, smul_zero] at hs hf
  obtain ⟨v, hV⟩ := ((hp.owes 1).pay)
  apply sub_eq_zero.mp
  apply Dtotal (Touch_near (hp.owes 1 |>.stay x) (hp.owes 1 |>.stay y) hs hf (hV x) (hV y))
  rw [Pi.sub_apply, hs.1, hf.1]
  apply sub_eq_zero.mpr
  exact funext fun z => Eq.trans (point₁ h x (core G) z) (point₁ h y (core G) z).symm

omit h hp in
private lemma path_one (i : ℕ) (w : Legs (Lane4 G))
    (H :
      ∀ j,
        j ∈ Domain.paths i 1 →
          tree parity (Cpu G t) (X (i - j) x t) (X j x t) w =
            tree parity (Cpu G t) (X (i - j) y t) (X j y t) w) :
    path (1 / 2) i 1 X X x t w = path (1 / 2) i 1 X X y t w := by
  unfold path
  simp only [Pi.smul_apply, Finset.sum_apply]
  refine congr_arg ((1 / 2 : ℝ) • ·) (Finset.sum_congr rfl ?_)
  exact H

omit h in
private lemma const_Δ (n : ℕ) (hn : 0 < n) (w : List (Lane4 G))
    (H : ∀ t, (path (1 / 2) n 1 X X x t w) = (path (1 / 2) n 1 X X y t w))
    (hv : ∀ t, ∀ v : Legs (Lane4 G), v.length = w.length + 2 → X n x t v = X n y t v) :
    X n x t w - X n y t w = run (style G T x n) w - run (style G T y n) w := by
  obtain he := hp.recu n hn x
  obtain ht := hp.recu n hn y
  let F (t : ℝ) := X n x t w - X n y t w
  have hs (t : ℝ) : HasDerivAt F 0 t := by
    obtain hq := ((he.2 t) w).sub (ht.2 t w)
    simp only [Pi.add_apply] at hq
    rw [H t, cycle_eq ((hp.owes n).stay x |>.joint) ((hp.owes n).stay y |>.joint) t w (hv t),
      sub_self] at hq
    exact hq
  rw [show X n x t w - X n y t w = F 0 from constancy hs t]
  unfold F
  rw [he.1, ht.1]

lemma equal_four (w : List (Lane4 G)) (hw : w.length = 4) : X 2 x t w = X 2 y t w := by
  have hP (t : ℝ) : path (1 / 2) 2 1 X X x t w = path (1 / 2) 2 1 X X y t w := by
    apply path_one x y t 2 w
    intro i hi
    have hz : i = 1 := by
      have hh := path_in hi
      omega
    rw [hz, show (2 : ℕ) - 1 = 1 from rfl, equal_full_one h hp x y]
  apply sub_eq_zero.mp
  rw [const_Δ hp x y t 2 (by decide) w hP
      (fun t l hl => (vacant h hp x t 2 l (by omega)).trans (vacant h hp y t 2 l (by omega)).symm)]
  unfold style
  rw [point₂ h x, point₂ h y, show run (core G 0) w = 0 from oneRank (participates G 0) w (by omega),
    mul_zero, mul_zero, sub_self]

lemma equal_five (w : List (Lane4 G)) (hw : w.length = 5) : X 3 x t w = X 3 y t w := by
  have hP (t : ℝ) : path (1 / 2) 3 1 X X x t w = path (1 / 2) 3 1 X X y t w := by
    apply path_one x y t 3 w
    intro i hi
    have he (u : Legs (Lane4 G)) (_hx : u.length = 3) : X 1 x t u = X 1 y t u := by
      rw [equal_full_one h hp x y]
    apply
      tree_top_eq (A := X (3 - i) x t) (H := X (3 - i) y t) (c := 5) _ (Pc_b x hp h _ t)
        (Pc_b x hp h _ t) (Pc_b y hp h _ t) (Pc_b y hp h _ t) _ _ _ w hw
    all_goals
      have hx := path_in hi
      obtain rfl | rfl := (show i = 1 ∨ i = 2 from by omega)
    all_goals
      first
      | exact rfl
      | exact he
      | exact equal_four h hp x y t
  apply sub_eq_zero.mp
  rw [const_Δ hp x y t 3 (by decide) w hP
      (fun t l hl => (vacant h hp x t 3 l (by omega)).trans (vacant h hp y t 3 l (by omega)).symm)]
  unfold style
  rw [point₃ h x, point₃ h y, show run (core G 1) w = 0 from oneRank (participates G 1) w (by omega),
    mul_zero, mul_zero, sub_self]

lemma origin_square (w : List (Lane4 G)) (hl : w.length = 2) :
    X 2 x t w - X 2 y t w = run (style G T x 2) w - run (style G T y 2) w := by
  apply const_Δ hp x y t 2 (by decide) w _ (fun t l hQ => equal_four h hp x y t l (by omega))
  intro u
  apply path_one ..
  intro i hi
  obtain hi := path_in hi
  rw [show i = 1 from by omega, show (2 : ℕ) - 1 = 1 from rfl, equal_full_one h hp x y]

omit h hp in
private lemma spike_off (i j : BH G) (t : ℝ) : Cpu G t i j (0 : QP) = 0 := by
  rcases i with ⟨⟨_ | a, _ | _⟩, i⟩ <;> rcases j with ⟨⟨_ | b, _ | _⟩, j⟩ <;>
    simp [Cpu, LegsK, Landau.choir, L0, Momentum.wave, theta, Momentum.sq, precision, delta]

omit h hp in
lemma tree_spike {S T : Law G} (w : List (Lane4 G)) (hv : ∀ i ∈ w, i.2 = 0) {K : Flux (BH G) QP ℂ}
    (hp : ∀ i j, K i j 0 = 0) : tree parity K S T w = 0 := by
  rw [tree, scatter_congr _ w _ (fun _ _ => (0 : ℂ)) ?_]
  exact map_zero (allocate ..)
  intro l r hh
  have hx i (he : i ∈ l) : (i.2 : QP) = 0 :=
    hv _ (List.Perm.mem_iff (split_perm hh) |>.mp (List.mem_append.mpr (Or.inl he)))
  unfold attaches
  have he : net l = 0 := by
    exact
      List.sum_eq_zero
        (fun _ hi => by
          obtain ⟨i, h, rfl⟩ := List.mem_map.mp hi
          exact hx i h)
  simp [he, hp]

lemma origin_SCC (a b c : G.ColorIndex) :
    X 3 x t (SCC G a b c) - X 3 y t (SCC G a b c) =
      (φC T x - φC T y + (Cx T x - Cx T y)) * (LieColor a b c : ℂ) := by
  rw [← varied_S h x y a b c]
  apply const_Δ hp x y t 3 (by decide) (SCC G a b c) _ (fun t l hQ => equal_five h hp x y t l hQ)
  intro t
  apply path_one ..
  intro i hi
  have hx i (hv : i ∈ SCC G a b c) : i.2 = 0 := by
    simp only [SCC, List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> rfl
  exact
    Eq.trans (tree_spike (SCC G a b c) hx (fun i j => spike_off i j t))
      (tree_spike (SCC G a b c) hx (fun i j => spike_off i j t)).symm
end YM.WilsonMS.BetaValue
