import YM.Integration.MSFilteredWordReadout

/-! Literal two-receiver congruence of both original finite Wilson
functionals. No assumption on the changing fees is used here. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.MSFiniteReceiverMatrix

open Matrix Finset Filter Function FVA2 MS MS.Local.Physical MS.Menus MS.Land
open MS.Dial MSPhysicalDeckChange MSFeeReadout MSNormalizedFeeReadout MSCommonMeasuredRows
open MSMeasuredFeeField MSFilteredWordReadout
open scoped Classical BigOperators

variable {G : Gauge} {A B : Deck G} {I : Type}
variable (V : Warehouse G) (P : Prescription A) (E : Fees B A) (h : ℕ)

def slotEquiv : Slots A (fun _ : Fin 2 => h) Finset.univ ≃ Glyph A h × Glyph A h where
  toFun a := (a ⟨0, Finset.mem_univ _⟩, a ⟨1, Finset.mem_univ _⟩)
  invFun a i := ![a.1, a.2] i.val
  left_inv a := by
    funext i
    rcases i with ⟨i, hi⟩
    fin_cases i <;> rfl
  right_inv _ := rfl

def identification (A B : Deck G) (h : ℕ) : Glyph B h ≃ Glyph A h :=
  Equiv.sigmaCongrRight fun i => Equiv.sigmaCongrRight fun j =>
    finCongr (MSPhysicalDeckChange.coordinates B A i.val j.val).finrank_eq

theorem grade (i : Glyph B h) : (identification A B h i).size = i.size := rfl

def matrix (μ θ : ℝ) : Matrix (Glyph B h) (Glyph A h) (PowerSeries ℂ) :=
  fun b a => charged P E μ θ b a

def source (T : Trial I (Fin 2)) (μ : ℝ) (j : I) : Matrix (Glyph A h) (Glyph A h) (PowerSeries ℂ) :=
  fun a b => native V P (ColorCode.labelAt A ∘ ![a,b]) T μ j

def target (T : Trial I (Fin 2)) (μ : ℝ) (j : I) : Matrix (Glyph B h) (Glyph B h) (PowerSeries ℂ) :=
  fun a b => marked V P E (ColorCode.labelAt B ∘ ![a,b]) T μ j

theorem pair {S : Type*} [CommMonoid S]
    (f : ↥(Finset.univ : Finset (Fin 2)) → S) :
    ∏ i, f i = f ⟨0, Finset.mem_univ _⟩ * f ⟨1, Finset.mem_univ _⟩ := by
  let L : Fin 2 → S := fun i => f ⟨i, Finset.mem_univ i⟩
  change (∏ i ∈ (Finset.univ : Finset (Fin 2)).attach, L i.val) = _
  rw [Finset.prod_attach, Fin.prod_univ_two]

theorem measured (T : Trial I (Fin 2)) (μ : ℝ) (j : I) :
    target V P E h T μ j =
      matrix P E h μ (T.profile.θ j) * source V P h T μ j *
        (matrix P E h μ (T.profile.θ j)).transpose := by
  classical
  apply Matrix.ext
  intro b c
  change marked V P E (ColorCode.labelAt B ∘ ![b,c]) T μ j = _
  rw [MSFilteredWordReadout.actual V P E μ T j ![b,c]]
  let F (a : Slots A (fun _ : Fin 2 => h) Finset.univ) :=
    (∏ i : (Finset.univ : Finset (Fin 2)),
      charged P E μ (T.profile.θ j) (![b,c] i.val) (a i)) *
      native V P (word (fun _ : Fin 2 => h) a) T μ j
  change (∑ a, F a) = _
  rw [← Equiv.sum_comp (slotEquiv (A := A) h).symm F, Fintype.sum_prod_type]
  simp only [F, pair, slotEquiv, Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  change (charged P E μ (T.profile.θ j) b d * charged P E μ (T.profile.θ j) c a) *
    source V P h T μ j d a = (charged P E μ (T.profile.θ j) b d * source V P h T μ j d a) *
      charged P E μ (T.profile.θ j) c a
  exact mul_right_comm _ _ _

theorem window_sum {R : Type*} [AddCommMonoid R] (h : ℕ) (f : Glyph A (h+1) → R) :
    ∑ a, f a = (∑ a : Glyph A h, f (MSFeeCoordinates.extend (Nat.le_succ h) a)) +
      ∑ a : Plaid A (h+1), f (Land.read a) := by
  rw [Fintype.sum_sigma, Fin.sum_univ_castSucc]
  apply congrArg₂ (· + ·)
  · conv_rhs => rw [Fintype.sum_sigma]
    rfl
  · rfl

def lowerPort (μ θ : ℝ) : Matrix (Plaid B (h+1)) (Glyph A h) (PowerSeries ℂ) :=
  fun b a => charged P E μ θ (Land.read b) a

def samePort (μ θ : ℝ) : Matrix (Plaid B (h+1)) (Plaid A (h+1)) (PowerSeries ℂ) :=
  fun b a => charged P E μ θ (Land.read b) (Land.read a)

def lowData (T : Trial I (Fin 2)) (μ : ℝ) (j : I) :
    Matrix (Plaid A (h+1)) (Glyph A h) (PowerSeries ℂ) :=
  fun b a => source V P (h+1) T μ j (Land.read b) (MSFeeCoordinates.extend (Nat.le_succ h) a)

def highData (T : Trial I (Fin 2)) (μ : ℝ) (j : I) :
    Matrix (Plaid B (h+1)) (Glyph B h) (PowerSeries ℂ) :=
  fun b a => target V P E (h+1) T μ j (Land.read b) (MSFeeCoordinates.extend (Nat.le_succ h) a)

theorem higher_zero (μ θ : ℝ) (b : Glyph B h) (a : Plaid A (h+1)) :
    charged P E μ θ (MSFeeCoordinates.extend (Nat.le_succ h) b) (Land.read a) = 0 := by
  rw [charged, above, map_zero, map_zero, mul_zero]
  exact Nat.lt_succ_of_le (MSFeeCoordinates.remaining b)

private theorem trim {R X : Type*} [Semiring R] (h : ℕ) (Z : Matrix X (Glyph A (h+1)) R)
    (U : Matrix (Glyph B (h+1)) (Glyph A (h+1)) R) (i : X) (c : Glyph B h)
    (hz : ∀ a : Plaid A (h+1), U (MSFeeCoordinates.extend (Nat.le_succ h) c) (Land.read a) = 0) :
    (Z * U.transpose) i (MSFeeCoordinates.extend (Nat.le_succ h) c) =
      ∑ a : Glyph A h, Z i (MSFeeCoordinates.extend (Nat.le_succ h) a) *
        U (MSFeeCoordinates.extend (Nat.le_succ h) c) (MSFeeCoordinates.extend (Nat.le_succ h) a) := by
  rw [Matrix.mul_apply, window_sum h]
  simp only [Matrix.transpose_apply, hz, mul_zero, Finset.sum_const_zero, add_zero]

private theorem extend_source (T : Trial I (Fin 2)) (μ : ℝ) (j : I) (x y : Glyph A h) :
    source V P (h+1) T μ j (MSFeeCoordinates.extend (Nat.le_succ h) x)
      (MSFeeCoordinates.extend (Nat.le_succ h) y) = source V P h T μ j x y := by
  apply congrArg (fun w : Fin 2 → MS.Rake.Label A => native V P w T μ j)
  funext i
  fin_cases i <;> rfl

private theorem inner (T : Trial I (Fin 2)) (μ : ℝ) (j : I) (b : Plaid B (h+1)) (a : Glyph A h) :
    (matrix P E (h+1) μ (T.profile.θ j) * source V P (h+1) T μ j) (Land.read b)
      (MSFeeCoordinates.extend (Nat.le_succ h) a) =
      (lowerPort P E h μ (T.profile.θ j) * source V P h T μ j +
        samePort P E h μ (T.profile.θ j) * lowData V P h T μ j) b a := by
  let e := MSFeeCoordinates.extend (B := A) (Nat.le_succ h)
  let M := matrix P E (h+1) μ (T.profile.θ j)
  let D := source V P (h+1) T μ j
  let g (x : Glyph A (h+1)) := M (Land.read b) x * D x (e a)
  let lo (x : Glyph A h) := lowerPort P E h μ (T.profile.θ j) b x * source V P h T μ j x a
  let hi (x : Plaid A (h+1)) := samePort P E h μ (T.profile.θ j) b x * lowData V P h T μ j x a
  have lower (x : Glyph A h) : g (e x) = lo x :=
    congrArg₂ (· * ·) rfl (extend_source V P h T μ j x a)
  have upper (x : Plaid A (h+1)) : g (Land.read x) = hi x := rfl
  change ∑ x, g x = (∑ x, lo x) + ∑ x, hi x
  exact (window_sum h g).trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun x _ => lower x)
    (Finset.sum_congr rfl fun x _ => upper x))
/-- The lower receiver is independently prescribed on the original two-port finite report. -/
theorem rectangle (T : Trial I (Fin 2)) (μ : ℝ) (j : I) :
    highData V P E h T μ j =
      (lowerPort P E h μ (T.profile.θ j) * source V P h T μ j +
        samePort P E h μ (T.profile.θ j) * lowData V P h T μ j) *
        (matrix P E h μ (T.profile.θ j)).transpose := by
  apply Matrix.ext
  intro b c
  let e := MSFeeCoordinates.extend (B := B) (Nat.le_succ h)
  let U := matrix P E (h+1) μ (T.profile.θ j)
  let Z := U * source V P (h+1) T μ j
  have hp : highData V P E h T μ j b c = (Z * U.transpose) (Land.read b) (e c) :=
    congrArg (fun X : Matrix (Glyph B (h+1)) (Glyph B (h+1)) (PowerSeries ℂ) => X (Land.read b) (e c))
      (measured V P E (h+1) T μ j)
  refine hp.trans ((trim h Z U (Land.read b) c (fun a => higher_zero P E h μ (T.profile.θ j) c a)).trans ?_)
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun a _ => congrArg₂ (· * ·) (inner V P E h T μ j b a) rfl

end YM.Integration.MSFiniteReceiverMatrix
