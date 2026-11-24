import YM.WilsonMS.Columns.LoopData
/-!
# Bare coupling/substitution and high-score rankings

Work with entries assigned one at a time. Show the unmarked choices
can be made with definite parity, *before* any finite scheme coordinate
reparametrization. Will give `g_*²κ(g²)=g²` per cut, while working with
power series in `g` throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.LoopRank
open MS Function Filter Set Finset MeasureTheory Metric
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Real Frame Wire Color Detect Native
  Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal
open PowerSeries (coeff)
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {b : Bool} {k i j n r : ℕ} {u v : ℤ} (x : ℝ)

section

structure Modal (i : ℕ) (p : Plan) : Prop where
  wave : ¬Allows i 0 → p.waveA = 0 ∧ p.waveC = 0
  shift : ¬Allows i 1 → p.coupling = 0

abbrev Valid (P : Team) :=
  ∀ i, Modal i (P i)
variable {p : Team}

def rulesPS (x : Cn) (k : ℕ) : Prop :=
  ∀ j, ¬Allows j k → coeff j x = 0

lemma rulesPS.pair {a b : Cn} {k l : ℕ} (h : rulesPS a k) (he : rulesPS b l) :
    rulesPS (a * b) (k + l) := by
  intro i hv
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun j hj => ?_
  by_cases hx : Allows j.1 k
  swap
  · rw [h _ hx, zero_mul]
  rw [he j.2 (fun t => hv (mem_antidiagonal.mp hj ▸ hx.sum t)), mul_zero]

lemma rulesPS.invUnit {a : Cn} (h : rulesPS a 0) : rulesPS (PowerSeries.invOfUnit a 1) 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hN
    have hx : i ≠ 0 := fun h => hN (h ▸ Allows.equal 0)
    rw [PowerSeries.coeff_invOfUnit i, if_neg hx]
    rw [Finset.sum_eq_zero, mul_zero]
    intro k hk
    split
    rename_i he
    · by_cases hQ : Allows k.2 0
      rw [h _ (fun hr => hN (Finset.mem_antidiagonal.mp hk ▸ hr.sum hQ)), zero_mul]
      rw [ih _ he hQ, mul_zero]
    rfl

lemma rulesPS.one : rulesPS 1 0 := fun i h => by
  rw [PowerSeries.coeff_one, if_neg (fun (t : i = 0) => h (t ▸ Allows.equal 0))]

lemma rulesPS.plow {a : Cn} (h : rulesPS a 1) (i : ℕ) : rulesPS (a ^ i) i := by
  induction i with
  | zero => simpa using rulesPS.one
  | succ i ih =>
    rw [pow_succ]
    exact ih.pair h

lemma φ_odd (he : Valid p) : rulesPS (Program.shift p x) 1 := by
  intro i hv
  rw [Program.shift, PowerSeries.coeff_mk]
  split
  rfl
  split
  rename_i he
  exact (hv (he ▸ Allows.equal 1)).elim
  rw [(he i).shift hv, Polynomial.eval_zero, Complex.ofReal_zero]

lemma Z_even (he : Valid p) (a : Atom Axis) : rulesPS (adap p a x) 0 := by
  have hx (P : ℕ → Poly) (hp : ∀ i, ¬Allows i 0 → P i = 0) : rulesPS (affirmative P x) 0 := by
    intro i hv
    rw [affirmative, PowerSeries.coeff_mk, if_neg (fun (t : i = 0) => hv (t ▸ Allows.equal 0)),
      hp i hv, Polynomial.eval_zero, Complex.ofReal_zero]
  have hC := hx (fun i => (p i).waveC) (fun i H => ((he i).wave H).2)
  have hA := hx (fun i => (p i).waveA) (fun i H => ((he i).wave H).1)
  rcases a with ⟨_ | _, _ | _⟩ <;>
    first
    | exact hA
    | exact hC
    | exact hA.invUnit
    | exact hC.invUnit
end
section arche
open Cylinder Lab Taylor Draft Orientation
variable {A : Type} {H : T (Cyl A ℂ)} {F : T (Dot G Cover)} {p : Team}

lemma wob_grade (he : Valid p) (hx : ∀ i, pays (i + k) (F i).val) :
    ∀ i, pays (i + k) (wobble G p x F i).val := by
  let Y := Program.shift p x
  let S (u : LightMode G Cover) := fieldV p x u.1
  have hF (l : List (LightMode G Cover)) : rulesPS (l.map S).prod 0 := by
    induction l with
    | nil => exact rulesPS.one
    | cons a l h => exact (Z_even x he a.1.1).pair h
  have hK (j : ℕ) : pays (j + k) (substitute Y F j).val := by
    rw [rules, sum_stack]
    refine sums _ fun i _ => ?_
    by_cases ha : Allows j i
    · exact higher (ha.sum (.equal k)) (scales (hx i) (Program.cut Y i j))
    rw [show cut Y i j = 0 from ((φ_odd x he).plow i) j ha, zero_smul]
    exact fun _ _ => rfl
  intro j
  rw [wobble, LinearMap.comp_apply, rolls, sum_stack]
  refine sums _ fun i hi => ?_
  intro u h
  rw [train_v, offer]
  by_cases hq : Allows i.1 0
  swap
  · change coeff i.1 (List.map S u).prod * _ = _
    rw [hF u _ hq, zero_mul]
  rw [show (substitute (Program.shift p x) F i.2).val u = 0 from hK i.2 u (fun he => h ?_), mul_zero]
  apply Allows.paid _ he
  convert hq.sum (Allows.equal (i.2 + k)) using 1 <;>
    (first
      | omega
      | ( obtain hv := Finset.mem_antidiagonal.mp hi
          omega))

lemma style_valid (h : Valid p) (k : ℕ) : pays (k + 2) (style G p x k).val :=
  wob_grade x h (F := core G)
    (fun i =>
      sum
        (LoopRank.full
          (by
            rw [Nat.cast_add]
            exact rankMod _ _))
        (LoopRank.higher (show Allows (i + 2) i from ⟨1, rfl⟩)
          (LoopRank.full
            (show Book.rank (↑i : ℤ) _ from fun l hl =>
              strange l
                (by
                  rw [mod_int] at hl
                  omega)))))
    k
end arche
section recurse
open Wind
variable {P H : Wind.Flow G}

lemma High_pays {p : Law G} (hs : Sat p P H) (h : TouchF P) (he : ∃ r, Wind.Rank P r) (hv : pays k p)
    (hp : ∀ t, pays k (H t)) : ∀ s, pays k (P s) := by
  obtain ⟨v, hv'⟩ := he
  let m := v.toNat + 1
  have hZ (n : ℕ) (ht : n ≤ m) :
    ∀ w, n ≤ List.length w → ¬Allows k (List.length w) → ∀ t, P t w = 0 := by
    induction ht using Nat.decreasingInduction with
    | self =>
      exact fun w hx _ t =>
        hv' t w
          (by
            unfold m at hx
            omega)
    | of_succ n hm ih =>
      intro w hw H' t
      refine Eq.trans (constancy (f := fun t : ℝ => P t w) (fun x => ?_) t) ?_
      · obtain hx := hs.2 x w
        change HasDerivAt _ (orbit (Cpu G x) μzone (P x) w + H x w) x at hx
        rw [finite_cc μzone (period0 μzone cour0 (main_f _) h), hp x w H', add_zero] at hx
        have he (q : QP) : trc (Cpu G x) q (P x) w = 0 := by
          rw [at_trc]
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          rw [ih ((i, q) :: (j, -q) :: w)
              (by
                simp
                omega)
              (fun H => H' (Allows.down H)),
            mul_zero]
        simpa [Ccy, he] using hx
      rw [hs.1, hv w H']
  exact fun t w hx => hZ 0 (by omega) w (by omega) hx t

lemma tree_p {a b c : ℕ} (hp : ∀ t, pays a (P t)) (ht : ∀ t, pays b (H t)) (hq : a + b = c + 2)
    (t : ℝ) : pays c (treeP G P H t) := by
  intro l hl
  change boulevard _ _ _ _ l = _
  rw [blvd, tree, scatter_congr _ l _ (fun _ _ => (0 : ℂ)) ?_]
  exact map_zero (allocate ..)
  intro x y hv
  obtain hX := split_length hv
  unfold attaches
  dsimp only
  apply Finset.sum_eq_zero
  intro i _
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases HH : Allows a (x.length + 1)
  swap
  · rw [hp t ((i, -net x) :: x) HH, hp t ((j, -net x) :: x) HH]
    ring
  have hL : ¬Allows b (y.length + 1) := by
    intro h'
    apply hl
    apply Allows.linear (c := 2)
    convert HH.sum h' using 1 <;> omega
  simp only [LinearMap.proj_apply]
  rw [ht t ((i, - -net x) :: y) hL, ht t ((j, - -net x) :: y) hL]
  ring

lemma into_run {A : Dot G Cover} (h : pays k A.val) : pays k (run A) := by
  intro l hl
  rw [← enough (F := run A) l rfl, ← Tone.grade, show Book.model l.length A = 0 from ?_, map_zero]
  rfl
  apply Subtype.ext
  ext i
  by_cases he : (i.length : ℤ) = l.length
  · exact
      (enough (F := A.val) i he).trans
        (h i (fun x => hl ((show i.length = l.length from by omega) ▸ x)))
  exact strange i he

variable {p : Team} {A Z : Dec G}

lemma Pc_b (hp : PC G p A) (hu : Valid p) (i : ℕ) (t : ℝ) : pays (i + 2) (A i x t) := by
  induction i using Nat.strong_induction_on generalizing t with
  | h i ih =>
    by_cases hz : i = 0
    swap
    · obtain ⟨v, hv⟩ := (hp.owes i).pay
      apply
        High_pays (hp.recu i (by omega) x) ((hp.owes i).stay x).joint ⟨_, hv x⟩
          (into_run (style_valid _ hu _))
      intro l
      rw [Wind.path, Pi.smul_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply]
      refine
          scales
            (sums (Domain.paths i 1) fun j hj =>
              tree_p (c := i + 2) (fun t => ih (i - j) ?_ t) (fun t => ih j (path_in hj).2 t) ?_ l)
            (((1 / 2 : ℝ) : ℂ)) <;>
        (first
          | omega
          | ( obtain he := path_in hj
              omega))
    rw [hz, hp.free]
    exact fun l _ => rfl

lemma Pm_b {F : Actor G} (hp : PM F A Z u) (hb : PC G p A) (hu : Valid p)
    (hq : ∀ i, pays (i + k) (F x i).val) (i : ℕ) (t : ℝ) : pays (i + k) (Z i x t) := by
  induction i using Nat.strong_induction_on generalizing t with
  | h i ih =>
    obtain ⟨v, hv⟩ := (hp.owes i).pay
    apply High_pays (hp.recu i x) ((hp.owes i).stay x).joint ⟨_, hv x⟩ (into_run (hq i))
    intro l
    rw [Wind.path, Pi.smul_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply]
    exact
      scales
        (sums (Domain.paths i 0) fun j hj =>
          tree_p (c := i + k) (fun t => Pc_b x hb hu (i - j) t) (fun t => ih j (path_in hj).2 t)
            (by
              obtain he := path_in hj
              omega)
            l)
        ((1 : ℝ) : ℂ)
end recurse
end YM.WilsonMS.LoopRank
