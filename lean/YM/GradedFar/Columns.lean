import YM.GradedFar.FormalDemand

/-!
# Grade-preserving running Far columns

The argument `η` in these column APIs is as in Scale.Law (so normally `-Real.log T`).
Use the geometry exponent index of `ChargeP` to keep track of every power T.
Use precisely the common MS mass convention `ν=Teller.logNu 1` of §F.
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Function Real PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {m d k : ℕ} {N : WilsonPrescription G}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}

/-- `η = -s`, `exp s = T` (the physical stretch; not to be confused with the
MS_Data binder) in our application. Includes the **positive** engineering power T^w.
Position argument η is held constant (including in `gaugeN`) throughout all coefficient operations.
-/
def Kseries (N : WilsonPrescription G) (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (d : ℕ) (η : ℝ) : Guard G d :=
  C (Level.Dial d η) * GroupS.gaugeN N.scheme N.criterion T (Teller.logNu 1) η d

local notation "B" => GroupS.gaugeN N.scheme N.criterion T (Teller.logNu 1)
lemma coeff_K (η : ℝ) : coeff k (Kseries N T d η) = Level.Dial d η * coeff k (B η d) :=
  coeff_C_mul ..
lemma Kfactor (η : ℝ) (v : Sec G d) : coeff k (Kseries N T d η) v =
    Level.Dial d η (coeff k (B η d) v) := by rw [coeff_K]; rfl

abbrev mode {G : Gauge} {d : ℕ} (f : ℕ → Sec G d) (b : Toon G d) : PowerSeries ℂ :=
  mk (fun j => coord b (f j))

lemma reconstructed (v : Sec G d) : ∑ c : Toon G d, coord c v • theory c = v :=
  all_sig v
lemma Dial_coord (b : Toon G d) (η : ℝ) (u : Sec G d) :
    coord b (Level.Dial d η u) = Score.fee η b.size * coord b u := by
  rw [← reconstructed u]
  simp_rw [map_sum, _root_.map_smul, Level.exact₀, _root_.map_smul, pivotδ, Score.season, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · subst i; simp only [smul_eq_mul]; ring
  simp

/-- Coordinate of a Far column on an arbitrary homogeneous output basis vector: actual
polynomial-budgeted `B` coordinate, multiplied by `C (T^grade)`.
-/
theorem column_grade_factor (b : Toon G d) (η : ℝ) (u : Sec G d) :
    mode (fun k => coeff k (Kseries N T d η) u) b =
      Acres η b.size * mode (fun k => coeff k (B η d) u) b := by
  ext k
  rw [coeff_C_mul, mode, mode, coeff_mk, coeff_mk, Kfactor, Dial_coord]

lemma length_power (b : Toon G d) (s : ℝ) :
    Score.fee (-s) b.size = (exp s:ℂ)^b.size := by
  rw [← Score.season, Extent.token, neg_neg]

lemma reconstructed_mode (f : ℕ → Sec G d) (k : ℕ) : ∑ c : Toon G d, coeff k (mode f c) • theory c = f k := by
  simp_rw [mode, coeff_mk]
  exact reconstructed (f k)

variable {e : Fin m → ℕ}
abbrev Choices (G : Gauge) {m : ℕ} (e : Fin m → ℕ) := (i : Fin m) → Toon G (e i)
abbrev Inputs (G : Gauge) {m : ℕ} (e : Fin m → ℕ) := (i : Fin m) → Sec G (e i)
abbrev Columns (G : Gauge) {m : ℕ} (e : Fin m → ℕ) := (i : Fin m) → ℕ → Sec G (e i)
def exterior (N : WilsonPrescription G) (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (η : ℝ) (v : Inputs G e) : Columns G e := fun i j => coeff j (Kseries N T (e i) η) (v i)

def factors (c : Choices G e) (X : Columns G e) : PowerSeries ℂ := ∏ i, mode (X i) (c i)
def roll (c : Choices G e) : Scan G m := fun i => flash (c i)

/-- We use coordinate sup norms on the fixed finite caps. Can take any fixed radius,
including the (closed) unit balls L=1. -/
def Within (L : ℝ) (u : Inputs G e) := ∀ i b, ‖coord b (u i)‖ ≤ L

lemma index_product {I J : Type} {k : ℕ} {f : J → I → ℝ → PowerSeries ℂ} (s : Finset J)
    (a : J → ℝ) (h : ∀ j ∈ s, ChargeP k (a j) (f j)) :
    ChargeP k (∑ j ∈ s, a j) (fun i t => ∏ j ∈ s, f j i t) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using
      (ChargeP.fixed (I:=I) (n:=k) (1:PowerSeries ℂ))
  | insert b s hb ih =>
    simp_rw [Finset.sum_insert hb, Finset.prod_insert hb]
    exact ChargeP.joint (h _ (Finset.mem_insert_self ..)) (ih fun j hj => h _ (Finset.mem_insert_of_mem hj))

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)
include H

lemma coefficient_preserves_grade (p : Toon G d) (η : ℝ) (i : ℕ) :
    Level.proj p.1 (coeff i (B η d) (theory p)) = coeff i (B η d) (theory p) := by
  have Q := (H.dilation (Teller.logNu 1)).check
  have he := (Level.graded_test _).mp (Q.ready η d i) (theory p) p.1
  rwa [Level.top] at he

/-- In particular none of the costs T^higher can occur in an input column
of a lower grade; in fact only precisely the same grade occurs. -/
lemma exact_grade (b p : Toon G d) (η : ℝ) (h : b.size ≠ p.size) :
    mode (fun k => coeff k (Kseries N T d η) (theory p)) b = 0 := by
  ext i
  rw [column_grade_factor, coeff_C_mul, mode, coeff_mk, ← coefficient_preserves_grade H p η i,
    sink _ b p h, mul_zero, map_zero]

lemma column_cap_compatible (h : d ≤ k) (η : ℝ) : Scale.Walk h (Kseries N T d η) (Kseries N T k η) := by
  intro i p
  have Q := (H.dilation (Teller.logNu 1)).check
  rw [Kfactor, Kfactor, Q.continues η h i p, Level.chain]

lemma column_unit (η : ℝ) (i : ℕ) :
    coeff i (Kseries N T d η) (leaf G d) = if i=0 then leaf G d else 0 := by
  have h := (H.dilation (Teller.logNu 1)).check.paid η d
  rw [Kfactor]; split_ifs with he
  · subst i; rw [h.zero, Module.End.one_apply, Level.Dial_leaf]
  rw [(h.high i he).1, map_zero]

lemma coeff_polynomial (b : Toon G d) (u : Sec G d) (k : ℕ) :
    Rhythm (fun (s : ℝ) => coord b (coeff k (B (-s) d) u)) := by
  obtain h := ((H.dilation (Teller.logNu 1)).check.proper d k u (coord b)).pre (-Polynomial.X)
  simpa only [Polynomial.eval_neg, Polynomial.eval_X] using h

lemma poly_column {I : Type} {L : ℝ} (b : Toon G d) (p : ℕ) (u : I → Sec G d)
    (hu : ∀ i c, ‖coord c (u i)‖ ≤ L) :
    ChargeP p 0 (fun i s => mode (fun k => coeff k (B (-s) d) (u i)) b) := by
  intro k _
  have h (s : ℝ) (i : I) : coeff k (mode (fun k => coeff k (B (-s) d) (u i)) b) =
        ∑ c : Toon G d, coord c (u i) * coord b (coeff k (B (-s) d) (theory c)) := by
    unfold mode; rw [coeff_mk]
    nth_rw 1 [← reconstructed (u i)]; simp_rw [map_sum,_root_.map_smul,smul_eq_mul]
  simp_rw [h]
  exact Rain.sum _ fun c _ => Rain.cover (Rain.cash ⟨L,fun i => hu i c⟩)
    (Rain.rhythm (coeff_polynomial H b (theory c) k))

lemma price_column {I : Type} {L : ℝ} (b : Toon G d) (u : I → Sec G d) (p : ℕ)
    (hu : ∀ i c, ‖coord c (u i)‖ ≤ L) :
    ChargeP p (-(b.size : ℝ)) (fun i s => mode (fun k => coeff k (Kseries N T d (-s)) (u i)) b) := by
  simp_rw [column_grade_factor]
  simpa only [add_zero] using ChargeP.joint (reflectV (a:=(b.size:ℝ))) (poly_column H b p u hu)

/-- Each term in the basis expansion incurs the sum of the engineering weights,
even grades charged with a repeated Far slot. Empty product = 1 also here. -/
theorem charge_columns {I : Type} {L : ℝ} (c : Choices G e) (u : I → Inputs G e) (p : ℕ)
    (hu : ∀ i, Within L (u i)) :
    ChargeP p (-(totalG (roll c):ℝ)) (fun i s => factors c (exterior N T (-s) (u i))) := by
  unfold totalG
  rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
  exact index_product _ _ fun j _ => price_column H (c j) (fun i => u i j) p (fun i => hu i j)
end
end YM.FVA2.GradedFar
