import YM.WilsonMS.Scales.Lowe
/-!
# Engineering conjugation of dilation arrays

Use `sweep t`: both pull positions (t positive zooms in on smaller distances)
and compensate the external engineering weight. No such transformation can
simply be commuted with frames; use the conjugation at every step. Work on
the point kernel side. No assertions on contact extensions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open PowerSeries (coeff mk X C constantCoeff)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G

abbrev watchD (G : Gauge) (d : ℕ) (x : ℝ) : Guard G d :=
  C (window G d x)

section burn
variable (G) (d : ℕ) (t r : ℝ)

lemma walk_o : watchD G d 0 = 1 := by rw [watchD, window0, map_one]

lemma walk_comp : watchD G d t * watchD G d r = watchD G d (t + r) := by
  unfold watchD
  rw [← map_mul, tower]

lemma unwound : IsUnit (window G d t) := by
  refine ⟨⟨window G d t, window G d (-t), ?_, ?_⟩, rfl⟩ <;>
    (first
      | rw [tower, add_neg_cancel, window0]
      | rw [tower, neg_add_cancel, window0])

lemma replenishes : Formal (watchD G d t) := by
  let e : Change G d := ⟨window G d t - 1, win_hold t⟩
  let F := watchD G d t
  have he : constantCoeff F = window G d t := PowerSeries.constantCoeff_C ..
  refine makeDeck e (he.symm ▸ unwound G d t) (he.trans ?_) (fun i hi => ?_)
  · ext1 p
    change _ = p + (window G d t p - p)
    abel
  rw [watchD, PowerSeries.coeff_C, if_neg hi]
  exact Submodule.zero_mem _

lemma Ladder.watches : Ladder (watchD G (d + 1) t) (watchD G d t) := by
  apply Ladder.C
  intro x
  suffices he :
    ∀ i : Pay d, window G _ t (step d (tileK G d i x)) = step d (window G d t (tileK G d i x))
    by
    rw [← whole x, map_sum, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he i
  intro i
  rw [← tile_up, pane, pane, tile_up]
  exact (map_smul ((step d).restrictScalars ℝ) _ _).symm
end burn
variable {A Q B : Guard G d}

abbrev buryD (s : ℝ) (R : Guard G d) :=
  watchD G d (-s) * R * watchD G d s

lemma deep_move (t : ℝ) (R : Guard G d) (n : ℕ) :
    coeff n (buryD t R) = window G d (-t) * coeff n R * window G d t := by
  rw [buryD, watchD, watchD, PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul]

lemma duties (s : ℝ) (h : CloseP A) : CloseP (buryD s A) := by
  refine ⟨Formal.product ((replenishes ..).product h.1) (replenishes ..), ?_⟩
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deep_move, h.zeroC, mul_one, tower,
    neg_add_cancel, window0]

lemma Clocks (t r : ℝ) (B : Guard G d) : buryD t (buryD r B) = buryD (r + t) B := by
  unfold buryD
  rw [← walk_comp G d r t, neg_add_rev, ← walk_comp]
  simp only [mul_assoc]

lemma wedge (t : ℝ) (R S : Guard G d) : buryD t (R * S) = buryD t R * buryD t S := by
  unfold buryD
  have he := walk_comp G d t (-t)
  rw [add_neg_cancel, walk_o] at he
  simp only [mul_assoc, ← mul_assoc (watchD G d t) (watchD G d (-t)), he, one_mul]

lemma on_time (s : ℝ) {A : Guard G d} (hp : Flat (coeff n A)) : coeff n (buryD s A) = coeff n A := by
  rw [deep_move]
  let Z := shadows (coeff n A)
  ext1 x
  have he (i : Pay d) :
    window G d (-s) (coeff n A (window G d s (tileK G d i x))) = coeff n A (tileK G d i x) := by
    let S := tag s i.val
    let Q := coeff n A
    let P := window G d (-s)
    let p := tileK G d i x
    have hL : tileK G d i (Q p) = Q p := by
      unfold Q p
      rw [← show Z = coeff n A from hp]
      unfold Z
      rw [tileskip, tileD, if_pos rfl]
    rw [pane]
    change P (Q (S • p)) = Q p
    rw [show Q (S • p) = S • Q p from map_smul (Q.restrictScalars ℝ) S p,
      show P (S • Q p) = S • P (Q p) from map_smul (P.restrictScalars ℝ) S (Q p)]
    nth_rw 1 [← hL]
    unfold P S
    rw [pane, smul_smul, tag_add]
    simp [tag, hL]
  rw [← whole x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => he i

lemma paceM (s : ℝ) (h : Mass A) : buryD s A = A :=
  PowerSeries.ext fun i => on_time s (Mass.exactly h i)

abbrev ChartK (G : Gauge) (d : ℕ) :=
  (n : ℕ) → Points n → Octave G d n

def Equad (F Q : ChartK G d) :=
  ∀ n : ℕ, EqOn (F n) (Q n) (conf n)
variable {F H Y : ChartK G d} {r s t : ℝ}

@[refl]
theorem Equad.rfl (F : ChartK G d) : Equad F F := fun _ _ _ => Eq.refl _

@[symm]
theorem Equad.symm (h : Equad F H) : Equad H F := fun _ _ hx => (h _ hx).symm

@[trans]
theorem Equad.trans (h : Equad F H) (hp : Equad H Y) : Equad F Y := fun _ _ hx =>
  (h _ hx).trans (hp _ hx)

def pullT (t : ℝ) (x : Points n) : Points n :=
  exp (-t) • x

lemma re_pose {x : Points n} (hx : x ∈ conf n) (t : ℝ) : pullT t x ∈ conf n := fun _ _ h =>
  hx (smul_right_injective E4 (exp_pos (-t)).ne' h)

lemma twice_pull (x : Points n) : pullT t (pullT s x) = pullT (s + t) x := by
  unfold pullT
  rw [smul_smul, ← exp_add]
  ring_nf

abbrev Sub (c : Cn) (F : ChartK G d) : ChartK G d := fun n x => Program.substitute c (F n x)

abbrev Act (F : ChartK G d) (A : Guard G d) : ChartK G d := fun n x => pivot A (F n x)

lemma Equad.sub (h : Equad F H) (c : Cn) : Equad (Sub c F) (Sub c H) := fun _ _ hv =>
  congr_arg _ (h _ hv)

lemma Equad.act (h : Equad F H) (A : Guard G d) : Equad (Act F A) (Act H A) := fun _ _ hv =>
  congr_arg _ (h _ hv)

lemma sub_subK (F : ChartK G d) {x y : Cn} (hx : Rooted x) (hy : Rooted y) :
    Sub y (Sub x F) = Sub (x.subst y) F :=
  funext fun _ => funext fun _ => ups _ hx hy

lemma action_unit (F : ChartK G d) : Act F 1 = F := by
  funext i x n
  ext1 v
  let G := F i x
  let A : Days i := Finsupp.single none n
  have ht : A ∈ Normalize.tally n i := by
    rw [totaled, Fintype.sum_option]
    simp [A]
  change pivot 1 (F i x) n v = _
  rw [pivot_cost, Finset.sum_eq_single_of_mem A ht]
  · rw [show A none = n from Finsupp.single_eq_same, show pulseU A 1 v = v from ?_]
    funext j
    unfold pulseU A
    rw [Finsupp.single_eq_of_ne (by simp), PowerSeries.coeff_one, if_pos rfl]
    rfl
  intro b hb hK
  obtain ⟨w, hW⟩ : ∃ x : Fin i, b (some x) ≠ 0 := by
    by_contra! he
    obtain hL := (totaled _).mp hb
    rw [Fintype.sum_option] at hL
    simp_rw [he, Finset.sum_const_zero, add_zero] at hL
    apply hK
    ext1 j
    cases j with
    | none => exact hL.trans (Finsupp.single_eq_same).symm
    | some j => simp [he, A]
  exact
    MultilinearMap.map_coord_zero _ (i := w)
      (by
        unfold pulseU
        rw [PowerSeries.coeff_one, if_neg hW, LinearMap.zero_apply])

lemma action_times (F : ChartK G d) (A P : Guard G d) : Act (Act F A) P = Act F (A * P) :=
  funext fun _ => funext fun _ => point_times ..

lemma action_sub {x : Cn} (h : Rooted x) (F : ChartK G d) (A : Guard G d) :
    Sub x (Act F A) = Act (Sub x F) (coupon x A) :=
  funext fun _ => funext fun _ => pointMove h A _

def sweep (s : ℝ) (F : ChartK G d) : ChartK G d :=
  Act (fun i x => F i (pullT s x)) (watchD G d s)

lemma exact_sweep (F : ChartK G d) (p : Points n) (v : Fin n → Sec G d) (j : ℕ) (t : ℝ) :
    sweep t F n p j v = F n (pullT t p) j ((window G d t) ∘ v) := by
  let A : Days n := Finsupp.single none j
  have ht : A ∈ Normalize.tally j n := by
    rw [totaled, Fintype.sum_option]
    simp [A]
  unfold sweep Act
  rw [pivot_cost, Finset.sum_eq_single_of_mem A ht]
  · rw [show pulseU A _ v = ((window G d t) ∘ v) from ?_]
    rw [show A none = j from Finsupp.single_eq_same]
    funext i
    unfold pulseU A watchD
    rw [Finsupp.single_eq_of_ne (by simp), PowerSeries.coeff_C, if_pos rfl]
    rfl
  intro b hb hK
  obtain ⟨w, hW⟩ : ∃ x : Fin n, b (some x) ≠ 0 := by
    by_contra! he
    obtain hL := (totaled _).mp hb
    rw [Fintype.sum_option] at hL
    simp_rw [he, Finset.sum_const_zero, add_zero] at hL
    apply hK
    ext1 k
    cases k with
    | none => exact hL.trans (Finsupp.single_eq_same).symm
    | some k => simp [he, A]
  exact
    MultilinearMap.map_coord_zero _ (i := w)
      (by
        unfold pulseU watchD
        rw [PowerSeries.coeff_C, if_neg hW, LinearMap.zero_apply])

lemma sweep_o (F : ChartK G d) : sweep 0 F = F := by
  funext i p j
  ext1 v
  rw [exact_sweep, window0]
  simp_rw [pullT, neg_zero, exp_zero, one_smul]
  rfl

lemma sweep_t (h : Equad F H) (t : ℝ) : Equad (sweep t F) (sweep t H) :=
  Equad.act (F := fun i x => F i (pullT t x)) (H := fun i x => H i (pullT t x))
    (fun i _ hx => h i (re_pose hx _)) _

lemma lands (s t : ℝ) (F : ChartK G d) : sweep t (sweep s F) = sweep (t + s) F := by
  unfold sweep
  change Act (Act _ _) _ = _
  rw [action_times, walk_comp, add_comm s t]
  unfold Act
  simp_rw [twice_pull]

lemma adjoint (s : ℝ) (F : ChartK G d) (P : Guard G d) :
    sweep s (Act F P) = Act (sweep s F) (buryD s P) := by
  unfold sweep
  let Q : ChartK G d := fun i x => F i (pullT s x)
  change Act (Act Q P) _ = _
  rw [action_times, action_times]
  congr 1
  unfold buryD
  rw [← mul_assoc, ← mul_assoc, walk_comp, add_neg_cancel, walk_o, one_mul]

lemma coupon_hold (c : Cn) (F : FieldEnd G d) : coupon c (C F) = C F := by
  apply PowerSeries.ext
  intro n
  unfold coupon
  simp only [PowerSeries.coeff_mk, rules, PowerSeries.coeff_C]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_Iic.mpr (Nat.zero_le _)), if_pos rfl, cut, pow_zero,
    PowerSeries.coeff_one]
  · split_ifs with h
    exact one_smul ℂ _
    exact zero_smul ℂ _
  intro b _ hb
  rw [if_neg hb, smul_zero]

lemma name_sub (t : ℝ) {c : Cn} (hv : Rooted c) (F : ChartK G d) :
    Sub c (sweep t F) = sweep t (Sub c F) := by
  unfold sweep
  rw [action_sub hv, watchD, coupon_hold]
end YM.WilsonMS.GFlow
