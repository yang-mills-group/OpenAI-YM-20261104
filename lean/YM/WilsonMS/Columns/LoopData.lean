import YM.WilsonMS.Stencil.JOptics
import YM.WilsonMS.Columns.LoopRanks
/-!
# Leg-counting on the MS prescription

Applies to the supplied MS choice of renormalized representatives. The height `h`
convention is separate from the loop/rank accounting; keep orders and ALL
poles in obtaining a power-selection fact on the Archive.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.LoopRank
open MS Function Filter Set Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
  _root_.YM.MS.Shine
open Hem Mell Logarithm Pearl Train Signal Book Convolve Garment.Wave Garment.Wick Dock Emit Detect
open Motif Literal Halo Mach Pole Outlook Native Lifting
open scoped Topology ContDiff Interval
variable {G : Gauge} {J k r d h n : ℕ} {z : ℝ}
section Ranks

private abbrev Uniform (p : ℤ) (U : Mield G n) : Prop :=
  ∀ i, Book.rank p (U i)

private lemma joint_R {p q : ℤ} {V X : Mield G n} (hp : Uniform p V) (hq : Uniform q X) :
    Uniform (p + q) (jaw G n V X) := by
  intro i
  rw [chew]
  exact Rails.sum _ fun j _ => Rails.sum _ fun k _ => ((hp j).product (hq k)).smul _

private lemma sum_R {p q : ℤ} {V X : Mield G n} (hp : Uniform p V) (hq : Uniform q X) :
    Book.rank (p + q) (sume V X) :=
  Rails.sum _ fun i _ => (hp i).product (hq i)

private lemma A_R (i : Arts.L n) : Uniform 1 (Motif.A n G i) := fun _ => mon_leaf _

private lemma c_R : Uniform 1 (cwave n G) := fun _ => mon_leaf _

private lemma blaze (z : Chan G n) : Book.rank 2 (blazeV G n z) := by
  rcases z with ⟨_ | a, i⟩
  exact (joint_R c_R c_R i).smul _
  exact joint_R (A_R a) c_R i

private lemma R₁ (i : Arts.L n) (j : Arts.L n) : Uniform 1 (F₀ i j : Mield G n) := fun _ =>
  rank_α _ _ _

private lemma Q_R (i j : Arts.L n) : Uniform 2 (quill i j : Mield G n) :=
  joint_R (A_R i) (A_R j)

private lemma R3 (G : Gauge) (n : ℕ) : Uniform 1 (cwave n G) ∧ Book.rank 3 (B₁ G n) := by
  refine
    ⟨c_R,
      Rails.add (?t : Book.rank 3 (top3 G n))
        (Rails.sum _ (fun i _ => ((mon_leaf (onX true i)).product (blaze i)).smul _))⟩
  refine Rails.smul _ (Rails.sum _ fun i _ => Rails.sum _ fun j _ => ?_)
  exact
    (sum_R (R₁ i j) (Q_R i j)).add
      (show Book.rank (1 + 2 : ℤ) (sume (quill i j) (F₀ i j)) from
        (sum_R (p := 2) (q := 1) (Q_R i j) (R₁ i j)))

private lemma R4 (G : Gauge) (n : ℕ) : Book.rank 4 (B₂ G n) :=
  Rails.smul _ (Rails.sum _ fun i _ => Rails.sum _ fun j _ => sum_R (Q_R i j) (Q_R i j))

lemma R_action (G : Gauge) (n m : ℕ) : Book.rank (n + 2) (pulseX G n m) := by
  rcases n with _ | (_ | (_ | k))
  · rw [Up0]
    exact Rails.zero
  · rw [pulse1]
    exact (R3 G m).2
  · rw [show pulseX G 2 = B₂ G from ?_]
    exact R4 G m
    simp [pulseX, Literal.hiss, χ]
  rw [show pulseX G (k + 1 + 1 + 1) = 0 from ?_]
  exact Rails.zero
  simp [pulseX, Literal.hiss, χ, Finsupp.single_eq_of_ne (show k + 1 + 1 + 1 ≠ 2 from by omega)]

private lemma head (G : Gauge) (i j : Axis) (x : List Axis) :
    ∃ Q : Box (Sky G),
      (∀ z n, Pole G n i j z x = value (Sky G) z Q n) ∧ ∀ k n : ℕ, Uniform (k + 1) (Q k n) := by
  classical
    induction x with
  | nil =>
    let A (n : ℕ) : Mield G n := F₀ (chair n i) (chair n j)
    let B (n : ℕ) : Mield G n := quill (chair n i) (chair n j)
    let Q := Finsupp.single 0 A + Finsupp.single (1 : ℕ) B
    refine ⟨Q, ?_, ?_⟩
    · simp_rw [Q, map_add, value_sl, pow_zero, pow_one, one_smul, Pi.add_apply, Pi.smul_apply]
      exact fun _ _ => rfl
    rintro (_ | (_ | k)) n
    all_goals simp [Q]
    · exact R₁ _ _
    · exact Q_R _ _
    exact fun _ => Rails.zero
  | cons a l ih =>
    obtain ⟨V, hv, hh⟩ := ih
    let s := Pole.spinD a G
    let L := boostD a G
    let Q := Boom 0 s V + Boom 1 L V
    refine ⟨Q, ?_, ?_⟩
    · intro z n
      dsimp only [Q]
      rw [Pole, hv, convoke, LinearMap.add_apply, LinearMap.smul_apply, map_add, linear_v _,
        show value _ _ (Boom 1 L V) = z • L (value _ _ V) from ?_]
      rfl
      rw [← Finsupp.sum_single V, Finsupp.sum]
      simp_rw [map_sum, Boom_sl, value_sl, pow_add, Finset.smul_sum, pow_one, map_smul, mul_smul]
    have he (k : ℕ) n : Uniform (↑k + 1) ((Boom 0 s V) k n) := by
      rw [← Literal.hiss, Literal.whole]
      intro i
      exact mon_apply (hh k n i) _
    intro k n c
    dsimp only [Q]
    rw [Finsupp.add_apply, Pi.add_apply, Pi.add_apply]
    refine (he k n c).add ?_
    have hp (k : ℕ) : Boom 1 L V (k + 1) = L (V k) := by
      rw [← Finsupp.sum_single V]
      simp only [Finsupp.sum, map_sum, Boom_sl, Finset.sum_apply']
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases he : k = j
      · subst j
        rw [add_comm 1, Finsupp.single_eq_same, Finsupp.single_eq_same]
      rw [Finsupp.single_eq_of_ne (by omega : k + 1 ≠ 1 + j), Finsupp.single_eq_of_ne he, map_zero]
    cases k with
    | zero =>
      rw [show Boom 1 L V 0 = 0 from ?_]
      exact Rails.zero
      rw [← Finsupp.sum_single V]
      simp only [Finsupp.sum, map_sum, Boom_sl, Finset.sum_apply']
      exact Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne (by omega : 0 ≠ 1 + j)
    | succ k =>
      rw [hp, show (↑(k + 1 : ℕ) + 1 : ℤ) = 1 + (↑k + 1 : ℤ) from by omega]
      exact joint_R (A_R _) (hh k n) c

private def Words (r : ℕ) (F : ℂ → Mob G) : Prop :=
  ∃ Q : Box (Mob G), F = (fun z => value _ z Q) ∧ ∀ n i : ℕ, Book.rank (↑n + ↑r) (Q n i)

private lemma legW (i : Plaq) (c : G.ColorIndex) :
    Words 1 (fun z n => Pole_leaf (G := G) (n := n) z i c) := by
  let U : Sky G →ₗ[ℂ] Mob G :=
    { toFun F n := F n c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  obtain ⟨p, hp, h⟩ := head G i.i i.j i.jets
  refine
    ⟨Boom 0 U p,
      funext
        (fun z => by
          rw [linear_v]
          exact funext fun m => congr_fun (hp z m) c),
      ?_⟩
  intro n i
  rw [← Literal.hiss, Literal.whole]
  exact h n i c

private lemma wingP (k : ℕ) (f : Fin k → Plaq) (σ : Grid G k) : Words k (Pole.wing k f σ) := by
  induction k with
  | zero =>
    let H : Mob G := fun _ => coin 1
    refine
      ⟨Finsupp.single 0 H,
        funext fun z =>
          (by
            rw [value_sl, pow_zero, one_smul]
            rfl),
        fun n i => ?_⟩
    by_cases hx : n = 0
    · subst n
      rw [Finsupp.single_eq_same]
      exact Rails.coin _
    rw [Finsupp.single_eq_of_ne hx]
    exact Rails.zero
  | succ k ih =>
    obtain ⟨Q, hQ, h⟩ := legW (f 0) (σ 0)
    obtain ⟨V, hv, hH⟩ := ih (f ∘ Fin.succ) (σ ∘ Fin.succ)
    refine ⟨Literal.root (LAMP G) Q V, funext fun z => funext fun n => ?_, fun j i => ?_⟩
    · rw [← pair_v]
      exact
        congr_arg₂ (bite n G |> fun t => fun x y => t x y) (congr_fun (congr_fun hQ z) n)
          (congr_fun (congr_fun hv z) n)
    rw [← Literal.hiss, Literal.pair_real, paired, Finset.sum_apply]
    refine Rails.sum _ fun p hp => ?_
    rw [show ↑j + ↑(k + 1 : ℕ) = (p.1 + 1 : ℤ) + (p.2 + k : ℤ) from
        (by
          obtain he := Finset.mem_antidiagonal.mp hp
          omega)]
    exact (h _ _).product (hH _ _)

private lemma W_add {p q : ℂ → Mob G} (H : Words r p) (hp : Words r q) : Words r (p + q) := by
  obtain ⟨X, rfl, hX⟩ := H
  obtain ⟨Q, rfl, hQ⟩ := hp
  exact ⟨X + Q, funext (fun i => (map_add ..).symm), fun n i => (hX n i).add (hQ n i)⟩

private lemma W_smul {p : ℂ → Mob G} (H : Words r p) (z : ℂ) : Words r (z • p) := by
  obtain ⟨X, rfl, hX⟩ := H
  exact ⟨z • X, funext (fun i => (map_smul (value ..) z X).symm), fun n i => (hX n i).smul z⟩

private lemma W0 : Words r (G := G) 0 :=
  ⟨0, funext fun _ => (map_zero (value ..)).symm, fun _ _ => Rails.zero⟩

private lemma W_sum {I : Type} (s : Finset I) (p : I → ℂ → Mob G) (h : ∀ i ∈ s, Words r (p i)) :
    Words r (∑ i ∈ s, p i) := by
  classical
    induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    exact W0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact W_add (h i (by simp)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma W_saint (k : ℕ) (f : Fin k → Plaq) (σ : Grid G k) : Words k (saint k f σ) := by
  rw [show saint k f σ = ∑ i : Grid G k, (Lifting.group G i σ : ℂ) • Pole.wing k f i from
      funext
        (fun z => by
          rw [Finset.sum_apply]
          rfl)]
  exact W_sum _ _ fun i _ => W_smul (wingP ..) _

lemma R_Marks {A : Law G} {X : Box (Mob G)} (he : Mach.Ele h n A X) :
    ∀ k i : ℕ, Book.rank (↑k + ↑n) (X k i) := by
  obtain ⟨ht, H⟩ := he
  obtain ⟨p, hp, hq⟩ : Words n (fun z => value _ z X) :=
    Submodule.span_induction (s := Sentence G n h) (R := ℝ) (p := fun f _ => Words n f)
      (by
        rintro u ⟨a, x, ha, rfl⟩
        exact W_saint _ _ _)
      W0 (fun _ _ _ _ => W_add) (fun c u _ h => W_smul h (c : ℂ)) ht
  have he z : value _ z X = value _ z p := congr_fun hp z
  obtain rfl : X = p :=
    (by
      apply sub_eq_zero.mp
      ext1 i
      funext m l
      exact
        valuedZ (X - p) (Garment.Wave.slice l) (fun z => by rw [map_sub, he, sub_self, map_zero]) i)
  exact hq
end Ranks
section read
variable {B : Local.Physical.Deck G} {A : Land.Booked B} (X : Land.MS_Data G A)

private lemma packed_sum {I : Type} {Z : I → Flats G} (s : Finset I) (h : ∀ i ∈ s, Carry k (Z i)) :
    Carry k (∑ i ∈ s, Z i) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact fun _ => (washed _).zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (washed _).plus (h i (mem_insert_self ..)) (ih fun j hj => h j (mem_insert_of_mem hj))

lemma action_fill (i : ℕ) : Carry (i + 2) (X.bulk i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    refine LoopRank.succ _ (X.bulkOK i) (invest G i) ?_ (pb_coal (fun i _ => gang (X.bulkOK i))) ?_
    · refine Eventually.of_forall fun _ => asks.mpr fun k => LoopRank.full ?_
      push_cast
      exact R_action G i k
    have he : Carry (i + 2) (∑ j ∈ shortB i, drive0 G (X.bulk j.1) (X.bulk j.2)) :=
      packed_sum _ fun j hj => by
        obtain ⟨hh, hj⟩ := mem_filter.mp hj
        exact
          LoopRank.heat (ih _ hj.1) (ih _ hj.2)
            (by
              obtain ht := Finset.mem_antidiagonal.mp hh
              omega)
    exact fun i' => (he i').mono fun _ hi => (pouch G (i + 2)).smul_mem _ hi

lemma mark_fill (s : Land.Plaid B h) (k : ℕ) : Carry (k + (Land.read s).grade) (X.marks h s k) := by
  let d := (Land.read s).grade
  induction k using Nat.strong_induction_on with
  | h k ih =>
    refine
      LoopRank.succ _ (X.markOK h s k) ((A.law h s).grows k) ?_
        (pm_coal (fun i _ => gang (X.markOK h s i)) (fun i => gang (X.bulkOK i))) ?_
    · exact
        Eventually.of_forall
          (fun i =>
            asks.mpr fun j =>
              LoopRank.full
                (by
                  rw [Nat.cast_add]
                  exact R_Marks (A.law h s) k j))
    exact
      packed_sum _ fun j hj => by
        obtain ⟨h0, hL⟩ := mem_filter.mp hj
        exact
          LoopRank.heat (action_fill X j.1) (ih _ hL)
            (by
              obtain he := Finset.mem_antidiagonal.mp h0
              omega)

lemma action_archive (n : ℕ) (x : ℝ × ℝ) : pays (n + 2) (Archive 4 X.bulk n x) :=
  asks.mp
    (valueC (gang (X.bulkOK n)).dost (Moony.toast (clockMoon (X.bulkOK n).1.choose_spec.2.1)) _
      (passes G _) (action_fill X n))
    0

lemma mark_archive (s : Land.Plaid B h) (n : ℕ) (x : ℝ × ℝ) :
    pays (n + (Land.read s).grade) (Archive h (X.marks h s) n x) :=
  asks.mp
    (valueC (gang ((X.markOK h s) n)).dost
      (Moony.toast (clockMoon ((X.markOK h s) n).1.choose_spec.2.1)) _ (passes G _) (mark_fill X s n))
    0
end read
end YM.WilsonMS.LoopRank
