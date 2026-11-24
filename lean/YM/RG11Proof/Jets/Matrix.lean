import YM.RG11Proof.Jets.Subst
/-!
# Frames at order horizon n on a fixed finite field horizon

The coefficients can be arbitrary ordinary PowerSeries. `squareInv` below
for example implements the triangular-by-order inverse of an identity-near
frame. No analytic inverse or source readout theorem here. The Lie constraints
(kill unit, H-equivariance, filtration etc) sit in a multiplication-closed
Submodule (`FrameLaw` in another file), not postulated on the inverse too.
`Matrix.BlockTriangular` in Mathlib uses the other convention; compose its
degree with `OrderDual.toDual` for our use. ALWAYS row i = coefficients of
image of field i. `FrameAt` pointwise multiplication is NOT the frame product;
use `Matrix` (application to fields in this convention is as row vectors).
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG11.Jets
open PowerSeries
open scoped BigOperators

variable {R S J K L : Type*}

abbrev Rect (J K R : Type*) := Matrix J K R
abbrev Square (J R : Type*) := Matrix J J R

/-- Inclusive truncated equality of formal matrices on a fixed finite
horizon (no engineering rescalings implicit). -/
def MatThrough [Semiring R] (n : ℕ) (A B : Rect J K R⟦X⟧) : Prop :=
  ∀ i j, Through n (A i j) (B i j)

def piece [Semiring R] (i : ℕ) (A : Rect J K R⟦X⟧) : Rect J K R := A.map (coeff i)
@[simp] theorem piece_apply [Semiring R] {i} {A : Rect J K R⟦X⟧} (j k) :
    piece i A j k = coeff i (A j k) := rfl

section mat
variable [Semiring R] (A B : Rect J K R⟦X⟧) (i : ℕ)

@[simp] theorem piece_zero : piece i (0 : Rect J K R⟦X⟧) = 0 := by
  ext j k
  simp
@[simp] theorem piece_add : piece i (A+B) = piece i A + piece i B := by ext j k; simp
@[simp] theorem piece_one [DecidableEq J] : piece i (1 : Square J R⟦X⟧) = if i=0 then 1 else 0 := by
  ext j k; split <;> rename_i hj <;> by_cases he : j=k <;> simp [Matrix.one_apply,hj,he,PowerSeries.coeff_one]

theorem piece_mul [Fintype K] (D : Rect K L R⟦X⟧) :
    piece i (A*D) = ∑ z∈Finset.HasAntidiagonal.antidiagonal i, piece z.1 A * piece z.2 D := by
  ext j k
  -- commute finite sums for the matrix product and convolution
  simp only [piece_apply, Matrix.mul_apply,map_sum,coeff_mul,Matrix.sum_apply]
  exact Finset.sum_comm

@[simp] theorem piece_zero_mul [Fintype K] (D : Rect K L R⟦X⟧) :
    piece 0 (A*D) = piece 0 A * piece 0 D := by simp [piece_mul]

def unpack (f : ℕ → Rect J K R) : Rect J K R⟦X⟧ := Matrix.of fun j k => mk (fun i => f i j k)

@[simp] theorem piece_unpack (f : ℕ→Rect J K R) : piece i (unpack f)=f i := by ext; simp [unpack]

theorem extPiece (h : ∀ i, piece i A=piece i B) : A=B := by
  ext j k i
  exact congrArg (fun (m:Rect J K R) => m j k) (h i)
end mat

namespace MatThrough
section
variable [Semiring R] {A B C D : Rect J K R⟦X⟧} {m n : ℕ}

theorem piece_eq (h : MatThrough n A B) (hm : m ≤ n) : piece m A = piece m B :=
  Matrix.ext fun i j => h i j m hm

theorem of_piece (h : ∀ m ≤ n, piece m A=piece m B) : MatThrough n A B :=
  fun i j m hm => congrArg (fun (u:Rect J K R) => u i j) (h m hm)

@[refl] theorem refl (A : Rect J K R⟦X⟧) : MatThrough n A A := fun _ _=>Through.refl _
@[symm] theorem symm (h : MatThrough n A B) : MatThrough n B A := fun _ _=>(h _ _).symm
theorem trans (h : MatThrough n A B) (hh : MatThrough n B C) : MatThrough n A C :=
  fun _ _=>(h _ _).trans (hh _ _)
theorem of_le (hl : m ≤ n) (h : MatThrough n A B) : MatThrough m A B :=
  fun i j=>Through.of_le hl (h i j)
theorem add (h : MatThrough n A B) (hc : MatThrough n C D) : MatThrough n (A+C) (B+D) :=
  fun i j=>(h i j).add (hc i j)

theorem mul [Fintype K] (h : MatThrough n A B) {C D : Rect K L R⟦X⟧} (hc : MatThrough n C D) :
    MatThrough n (A*C) (B*D) :=
  fun i j=>Through.sum fun k _=>(h i _).mul (hc k j)
end
end MatThrough

-- Identity-leading case gives recursive inverse at finite precision; works
-- over any Ring. Thus tracks admissible coefficient submodules as well as
-- what perturbative information is used.
section inverse
variable [Ring R] [Fintype J] [DecidableEq J]

def nearId (A : Square J R⟦X⟧) : Prop := piece 0 A = 1

omit [Fintype J] in
@[simp] theorem nearId_one : nearId (1:Square J R⟦X⟧) := by simp [nearId]

theorem nearId.mul {A B : Square J R⟦X⟧} (ha : nearId A) (hb : nearId B) : nearId (A*B) := by
  unfold nearId at *; simp [ha,hb]

/-- The sum of pieces involving strictly lower precision of the RIGHT factor.
Used at positive power order; `if` also specifies the degenerate n=0 sum. -/
def trail (f g : ℕ→Square J R) (n : ℕ) : Square J R :=
  ∑ z∈Finset.HasAntidiagonal.antidiagonal n, if z.1=0 then 0 else f z.1 * g z.2

def trailLeft (f g : ℕ→Square J R) (n : ℕ) : Square J R :=
  ∑ z∈Finset.HasAntidiagonal.antidiagonal n, if z.2=0 then 0 else f z.1 * g z.2

omit [DecidableEq J] in
private theorem decompCauchy (n : ℕ) (f g : ℕ → Square J R) :
    (∑ z∈Finset.HasAntidiagonal.antidiagonal n, f z.1 * g z.2) =
    f 0 * g n + trail f g n := by
  have H : f 0 * g n = ∑ z∈Finset.HasAntidiagonal.antidiagonal n, if z.1=0 then f z.1 * g z.2 else 0 := by
    rw [Finset.sum_eq_single_of_mem (0,n) (by simp) ?_]; rotate_left
    · rintro ⟨a,b⟩ hb hx
      have hw := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      dsimp at hw ⊢
      split
      · exfalso; apply hx; apply Prod.ext <;> dsimp <;> omega
      rfl
    simp
  rw [H,trail,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_; intro z _; split <;> simp

omit [DecidableEq J] in
private theorem decompCauchyLeft (n : ℕ) (f g : ℕ → Square J R) :
    (∑ z∈Finset.HasAntidiagonal.antidiagonal n, f z.1 * g z.2) =
    f n * g 0 + trailLeft f g n := by
  have H : f n * g 0 = ∑ z∈Finset.HasAntidiagonal.antidiagonal n, if z.2=0 then f z.1 * g z.2 else 0 := by
    rw [Finset.sum_eq_single_of_mem (n,0) (by simp) ?_]; rotate_left
    · rintro ⟨a,b⟩ hb hx
      have hw := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      dsimp at hw ⊢
      split
      · exfalso; apply hx; apply Prod.ext <;> dsimp <;> omega
      rfl
    simp
  rw [H,trailLeft,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_; intro z _; split <;> simp

omit [DecidableEq J] in
theorem piece_mul_recurse (A B : Square J R⟦X⟧) (n : ℕ) :
    piece n (A*B)=piece 0 A * piece n B + trail (piece · A) (piece · B) n := by
  rw [piece_mul]; exact decompCauchy n (piece · A) (piece · B)
omit [DecidableEq J] in
theorem piece_mul_recurse_left (A B : Square J R⟦X⟧) (n : ℕ) :
    piece n (A*B)=piece n A * piece 0 B + trailLeft (piece · A) (piece · B) n := by
  rw [piece_mul]
  exact decompCauchyLeft n (piece · A) (piece · B)

omit [DecidableEq J] in
private theorem trail_eq (f g h : ℕ→Square J R) (n : ℕ) (he : ∀ i<n, g i=h i) : trail f g n=trail f h n := by
  unfold trail; refine Finset.sum_congr rfl (fun z hZ=> ?_)
  have hv := Finset.HasAntidiagonal.mem_antidiagonal.mp hZ
  split
  · rfl
  rw [he _ (by omega)]
omit [DecidableEq J] in
private theorem trailLeft_eq (f g h : ℕ→Square J R) (n : ℕ) (he : ∀ i<n, g i=h i) : trailLeft g f n=trailLeft h f n := by
  unfold trailLeft; refine Finset.sum_congr rfl (fun z hZ=> ?_)
  have hv := Finset.HasAntidiagonal.mem_antidiagonal.mp hZ
  split
  · rfl
  rw [he _ (by omega)]

def invParts (A : Square J R⟦X⟧) (n : ℕ) : Square J R :=
  if n=0 then 1
  else - trail (piece · A) (fun i => if _:i<n then invParts A i else 0) n
termination_by n
private def invPartsLeft (A : Square J R⟦X⟧) (n : ℕ) : Square J R :=
  if n=0 then 1
  else - trailLeft (fun i => if _:i<n then invPartsLeft A i else 0) (piece · A) n
termination_by n

def squareInv (A : Square J R⟦X⟧) := unpack (invParts A)

@[simp] theorem squareInv_base (A : Square J R⟦X⟧) : nearId (squareInv A) := by
  unfold nearId squareInv; rw [piece_unpack,invParts]; simp

theorem squareInv_piece (A : Square J R⟦X⟧) (n : ℕ) (hn : 0<n) :
    piece n (squareInv A) = - trail (piece · A) (piece · (squareInv A)) n := by
  unfold squareInv; rw [piece_unpack,invParts,if_neg hn.ne']
  congr 1
  apply trail_eq (piece · A)
  intro i hi; simp [hi]

theorem mul_squareInv {A : Square J R⟦X⟧} (h : nearId A) : A*squareInv A = 1 := by
  apply extPiece; intro n; cases n with
  | zero => rw [piece_zero_mul, h, squareInv_base, one_mul,← nearId_one]
  | succ n => rw [piece_mul_recurse,h, one_mul,squareInv_piece _ _ n.zero_lt_succ, neg_add_cancel,piece_one]; simp

private theorem left_mul {A : Square J R⟦X⟧} (h : nearId A) : (unpack (invPartsLeft A)) * A=1 := by
  apply extPiece; intro n; cases n with
  | zero => unfold nearId at h; rw [piece_zero_mul, h,piece_one,piece_unpack,mul_one,invPartsLeft]; simp
  | succ n =>
    rw [piece_mul_recurse_left,h,mul_one,piece_one,if_neg (by omega)]
    let f : ℕ→Square J R := invPartsLeft A
    have he : piece (n+1) (unpack f) = - trailLeft (piece · (unpack f)) (piece · A) (n+1) := by
      rw [piece_unpack, show f (n+1)=invPartsLeft A (n+1) from rfl,invPartsLeft,if_neg (by omega)]; congr 1
      apply trailLeft_eq; intro i hi; simp [hi,f]
    exact (congrArg (· + trailLeft (piece · (unpack f)) (piece · A) (n+1)) he).trans (neg_add_cancel ..)

theorem squareInv_mul {A : Square J R⟦X⟧} (h : nearId A) : squareInv A*A=1 := by
  have he : unpack (invPartsLeft A) = squareInv A := left_inv_eq_right_inv (left_mul h) (mul_squareInv h)
  rw [←he]; exact left_mul h

theorem through_inverse_unique {n : ℕ} {A B : Square J R⟦X⟧} (h : nearId A)
    (hw : MatThrough n (A*B) 1) : MatThrough n B (squareInv A) := by
  have he := (MatThrough.refl (n:=n) (squareInv A)).mul hw
  rwa [← mul_assoc,squareInv_mul h,one_mul,mul_one] at he

theorem MatThrough.squareInv {n} {A B : Square J R⟦X⟧} (h : MatThrough n A B) (ha : nearId A) (hb : nearId B) :
    MatThrough n (Jets.squareInv A) (Jets.squareInv B) := by
  apply through_inverse_unique hb
  have he := h.mul (MatThrough.refl (Jets.squareInv A))
  rw [mul_squareInv ha] at he
  exact he.symm
end inverse
end YM.RG11.Jets
