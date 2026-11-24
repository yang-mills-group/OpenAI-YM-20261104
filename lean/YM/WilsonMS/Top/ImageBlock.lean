import YM.WilsonMS.Top.Image

/-! # Actual blocks of the finite Fourier-transformed inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Position
open Function Filter Finset Set Matrix Complex Lattice
open MS MS.Koszul MS.Plane MS.Native MS.Orbit MS.Orbit.Cog
open MS.Book MS.Landau MS.Latch MS.City MS.Swirl MS.Swirl.Near MS.Tone Bloch
open scoped Topology

variable (G : Gauge) (n : Side)
local notation "Γ" => fourier G n
local notation "K₀" => mat n (FinalK G)
local notation "A0" => straightA G n
local notation "L0" => straightL G n

private lemma drop_column {I : Type} [DecidableEq I] [Fintype I] (f : I → BH G)
    (W : FixedMode G n → ℂ) (i : I × Site n) :
    ∑ x : FixedMode G n, Γ (Prod.map f id i) x * W x =
      ∑ x : I × Site n, FFT.forward I n i x * W (Prod.map f id x) := by
  classical
  change (∑ x : BH G × Site n, _) = _
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type (α₁ := I),
    Finset.sum_eq_single_of_mem (f i.1) (mem_univ _),
    Finset.sum_eq_single_of_mem (s := Finset.univ) i.1 (mem_univ _)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [fourier, FFT.forward]
  · intro j _ hj
    simp [FFT.forward, Ne.symm hj]
  intro j _ hj
  simp [fourier, Ne.symm hj]

lemma angular_pull {I J : Type} [DecidableEq I] [DecidableEq J] [Fintype I] [Fintype J] (f : I → BH G)
    (g : J → BH G) (u : I × Site n) (v : J × Site n) (W : Grain (FixedMode G n))
    (X : Matrix (I × Site n) (J × Site n) ℂ)
    (h : ∀ a b, X a b = Chill W (Prod.map f id a) (Prod.map g id b)) :
    Chill (induce Γ W) (Prod.map f id u) (Prod.map g id v) =
      (FFT.forward I n * X * (FFT.forward J n)ᵀ) u v := by
  let Y (a : I × Site n) : FixedMode G n := Prod.map f id a
  let Z (b : J × Site n) : FixedMode G n := Prod.map g id b
  let C := FFT.forward I n
  let R := FFT.forward J n
  unfold Chill
  rw [induce_value]
  change 2 * (∑ j, ∑ i, Γ (Y u) i * W i j * Γ (Z v) j) = _
  calc
    _ = (∑ i, Γ (Y u) i * ∑ j, Γ (Z v) j * Chill W i j) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      unfold Chill
      ring
    _ = (∑ x : I × Site n, C u x * ∑ y : J × Site n, R v y * X x y) := by
      rw [drop_column G n f (fun i => ∑ j, Γ (Z v) j * Chill W i j)]
      simp_rw [h]
      refine Finset.sum_congr rfl fun i _ => congr_arg ((FFT.forward I n u i) * ·) ?_
      exact drop_column G n g (fun j => Chill W (Y i) j) _
    _ = _ := by
      simp_rw [Matrix.mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      unfold C R
      ring

lemma input_A (x y : SiteField G n) : Chill (initialK G n) (aa G n x) (aa G n y) = A0 x y :=
  angular_pull G n (atomA G) (atomA G) x y _ _ fun _ _ => rfl

lemma input_L (x y) : Chill (initialK G n) (cc G n x) (ak G n y) = -(L0 x y) := by
  unfold cc ak initialK straightL
  rw [angular_pull G n (atomC G) (atomK G) _ _ _ (-LK G n) (fun i j => neg_neg (Chill K₀ _ _)),
    Matrix.mul_neg, Matrix.neg_mul]
  rfl

abbrev LetterFull :=
  Darboux.Letters (SiteField G n) (GaugeField G n)

def includeF : LetterFull G n → FixedMode G n := fun x =>
  match x with
  | .inl (.inl i) => aa G n i
  | .inr (.inl i) => ak G n i
  | .inl (.inr i) => cc G n i
  | .inr (.inr i) => cb G n i

def eIso : LetterFull G n ≃ FixedMode G n :=
  { toFun := includeF G n
    invFun
      i :=
      match i with
      | (((some i, false), a), v) => Darboux.a ((i, a), v)
      | (((some i, true), a), v) => Darboux.k ((i, a), v)
      | (((none, false), a), v) => Darboux.c (a, v)
      | (((none, true), a), v) => Darboux.b (a, v)
    left_inv := by rintro ((⟨⟨i, a⟩, v⟩ | ⟨i, v⟩) | (⟨⟨i, a⟩, v⟩ | ⟨i, v⟩)) <;> rfl
    right_inv := by rintro ⟨⟨⟨_ | i, _ | _⟩, a⟩, v⟩ <;> rfl }

private lemma extra_zero {A B : Type} [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
    (f : A → BH G) (g : B → BH G) (h : ∀ i j p, Bass G (f i) (g j) p = 0) (x : A × Site n)
    (y : B × Site n) : Chill (initialK G n) (Prod.map f id x) (Prod.map g id y) = 0 := by
  unfold initialK
  rw [angular_pull G n f g _ _ _ 0 (fun i j => ?_)]
  simp
  change (0 : ℂ) = Chill K₀ (f _, i.2) (g _, j.2)
  unfold Chill mat
  split
  · simp only [EdgeV, FinalK, h, zero_div, mul_zero]
  rw [mul_zero]

set_option maxHeartbeats 600000 in
lemma straight_chill (x y : LetterFull G n) :
    Chill (initialK G n) (includeF G n x) (includeF G n y) = Darboux.covariance A0 L0 x y := by
  rcases x with (x | x) | (x | x) <;> rcases y with (y | y) | (y | y)
  · exact input_A G n x y
  · refine extra_zero G n (atomA G) (atomC G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomA G) (atomK G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomA G) (atomB G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomC G) (atomA G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomC G) (atomC G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · exact input_L G n x y
  · refine extra_zero G n (atomC G) (atomB G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomK G) (atomA G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine (traceS _ _ (basic_symmetry G n)).trans ?_
    change -1 * Chill _ (cc G n y) (ak G n x) = L0 y x
    rw [input_L, neg_one_mul, neg_neg]
  · refine extra_zero G n (atomK G) (atomK G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomK G) (atomB G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomB G) (atomA G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomB G) (atomC G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomB G) (atomK G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _
  · refine extra_zero G n (atomB G) (atomB G) ?_ x y
    intro i j p
    unfold Bass Landau.choir
    split
    exact mul_zero _
    exact mul_zero _

def reflectedE (x : SiteField G n) : SiteField G n :=
  (x.1, -x.2 - step x.1.1)

def reflectedG (x : GaugeField G n) : GaugeField G n :=
  (x.1, -x.2)

lemma involE : Involutive (reflectedE G n) := fun x => by simp [reflectedE]

lemma involG : Involutive (reflectedG G n) := fun x => by simp [reflectedG]

def flipE :=
  -Root.inclusion (reflectedE G n)

def flipU :=
  Root.inclusion (reflectedG G n)
local notation "XE" => flipE G n
local notation "XU" => flipU G n

lemma flipET : XEᵀ = XE := by
  rw [flipE, transpose_neg]
  congr 1
  ext i j
  rw [transpose_apply]
  unfold Root.inclusion
  simp_rw [show reflectedE G n i = j ↔ reflectedE G n j = i from (involE G n).eq_iff.trans eq_comm]

lemma flipUT : XUᵀ = XU := by
  ext i j
  rw [transpose_apply]
  unfold flipU Root.inclusion
  simp_rw [show reflectedG G n i = j ↔ reflectedG G n j = i from (involG G n).eq_iff.trans eq_comm]

lemma turnR {I : Type} (F : Matrix I (SiteField G n) ℂ) (i j) :
    (F * XE) i j = -F i (reflectedE G n j) := by
  rw [flipE, Matrix.mul_neg, Matrix.neg_apply, Root.col_inclusion]

lemma turnL {I : Type} (F : Matrix (SiteField G n) I ℂ) (i j) :
    (XE * F) i j = -F (reflectedE G n i) j := by
  rw [← flipET, flipE, transpose_neg, Matrix.neg_mul, Matrix.neg_apply, Root.row_inclusion]

lemma turnU {I : Type} (F : Matrix (GaugeField G n) I ℂ) (i j) :
    (XU * F) i j = F (reflectedG G n i) j := by
  rw [← flipUT]
  exact Root.row_inclusion _ _ _ _

lemma sym_C : A0ᵀ = A0 := by
  ext i j
  rw [transpose_apply, ← input_A, traceS _ _ (basic_symmetry G n), input_A]
  exact one_mul _

lemma image_A (x y : SiteField G n) :
    Chill (foldedK G n) (aa G n x) (aa G n y) = (A0 * (1 + XE)) x y := by
  unfold Chill
  rw [actual_image, _root_.mul_add, _root_.mul_left_comm 2]
  rw [show reflect G n (aa G n y) = aa G n (reflectedE G n y) from rfl]
  change Chill _ _ _ + (-1) * Chill _ _ _ = _
  rw [input_A, input_A, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, turnR, neg_one_mul]

lemma image_sym : (A0 * (1 + XE))ᵀ = A0 * (1 + XE) := by
  ext i j
  rw [transpose_apply, ← image_A, traceS _ _ (folded_symmetry G n), image_A]
  exact one_mul _

lemma mirrors : XE * A0 = A0 * XE := by
  obtain hp := image_sym G n
  rw [Matrix.mul_add, Matrix.mul_one, transpose_add, transpose_mul, sym_C G n, flipET G n] at hp
  exact add_left_cancel hp

lemma image_L (x : GaugeField G n) (y : SiteField G n) :
    Chill (foldedK G n) (cc G n x) (ak G n y) =
      -(((L0 * (1 + XE)) : Matrix (GaugeField G n) (SiteField G n) ℂ) x y) := by
  unfold Chill
  rw [actual_image, _root_.mul_add, _root_.mul_left_comm 2,
    show reflect G n (ak G n y) = ak G n (reflectedE G n y) from rfl]
  change Chill _ _ _ + (-1) * Chill _ _ _ = _
  rw [input_L, input_L, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, turnR]
  ring

lemma reachesE : XU * L0 = L0 * XE := by
  ext i j
  obtain hz := image_L G n i j
  rw [traceS _ _ (folded_symmetry G n)] at hz
  unfold Chill at hz
  rw [actual_image, _root_.mul_add, _root_.mul_left_comm 2, Matrix.mul_add, Matrix.mul_one,
    show reflect G n (cc G n i) = cc G n (reflectedG G n i) from rfl] at hz
  change
    -1 * (Chill _ (ak G n j) (cc G n i) + 1 * Chill _ (ak G n j) (cc G n (reflectedG G n i))) =
      _ at hz
  rw [traceS _ (cc G n i) (basic_symmetry G n), input_L,
    traceS _ (cc G n (reflectedG G n i)) (basic_symmetry G n), input_L] at hz
  rw [turnU]
  simp only [show σbranch (ak G n j) = true from rfl,
    show ∀ x, σbranch (cc G n x) = true from fun _ => rfl, cross_true, Matrix.add_apply] at hz
  linear_combination -hz

lemma image_chill (x y : LetterFull G n) :
    Chill (foldedK G n) (includeF G n x) (includeF G n y) =
      Darboux.covariance (A0 * (1 + XE)) (L0 * (1 + XE)) x y := by
  let A := A0 * (1 + XE)
  let L : Matrix (GaugeField G n) (SiteField G n) ℂ := L0 * (1 + XE)
  let r := reflectedE G n
  let v := reflectedG G n
  let f : LetterFull G n → LetterFull G n := Sum.map (Sum.map r v) (Sum.map r v)
  have he i j :
    Chill (foldedK G n) (includeF G n i) (includeF G n j) =
      Darboux.covariance A0 L0 i j +
        scalarSign G n (includeF G n j) * Darboux.covariance A0 L0 i (f j) := by
    unfold Chill
    rw [actual_image, _root_.mul_add, _root_.mul_left_comm 2, ← straight_chill, ← straight_chill,
      show includeF G n (f j) = reflect G n (includeF G n j) by
        rcases j with (j | j) | (j | j) <;> rfl]
  rcases x with (x | x) | (x | x) <;> rcases y with (y | y) | (y | y)
  case inl.inl.inl.inl => exact image_A G n x y
  case inl.inr.inr.inl => exact image_L G n x y
  case inr.inl.inl.inr =>
    change Chill _ (ak G n x) (cc G n y) = L y x
    rw [traceS _ _ (folded_symmetry G n), image_L]
    change -1 * (-(L y x)) = _
    rw [neg_one_mul, neg_neg]
  all_goals
    rw [he]
    change 0 + _ * (0 : ℂ) = 0
    rw [mul_zero, add_zero]
end YM.WilsonMS.Position
