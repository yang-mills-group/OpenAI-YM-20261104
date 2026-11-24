import YM.WilsonMS.Beta.Counterterm
/-!
# Pure interaction origin as the MS parameter varies

`Ax, Cx, φC`: the target amplitudes at log µ x. AA and CU words probe the
first two projections; SCC will test the orientation. Write the expression
for these projections and orders at given momenta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal Cylinder Lab Menus Lifting Landau.Detect.Mark
open PowerSeries (coeff)
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {T : Team} (h : Valid T) (x y : ℝ)

abbrev Punit :=
  Detect.spike 0

abbrev AA (G : Gauge) (i : G.ColorIndex) (q : QP) : Legs (Lane4 G) :=
  [Detect.W 1 i q, Detect.W 1 i (-q)]

abbrev CU (G : Gauge) (i : G.ColorIndex) (q : QP) : Legs (Lane4 G) :=
  [Detect.C i q, Detect.U 0 i (-q)]

abbrev SCC (G : Gauge) (a b c : G.ColorIndex) : Legs (Lane4 G) :=
  [Detect.S a 0, Detect.C b 0, Detect.C c 0]

abbrev φC (T : Team) (x : ℝ) :=
  coeff 3 (shift T x)

def Ax (T : Team) (x : ℝ) :=
  coeff 2 (affirmative (fun i => (T i).waveA) x)

def Cx (T : Team) (x : ℝ) :=
  coeff 2 (affirmative (fun i => (T i).waveC) x)
local notation "a(" x ")" => Ax T x
local notation "c(" x ")" => Cx T x
local notation "M_" i "(" x ")" => run (style G T x i)

lemma token_core (a b c : G.ColorIndex) : run (core G 1) (SCC G a b c) = LieColor a b c := by
  rw [← token_R]
  unfold Mark.token Menus.LE
  rw [skin_eq (j := 0) _ _ _ (by norm_num [fieldDim, wfield, dim, Detect.S, C, qnote, gaugeC, ghost]),
    torch_at]
  simp only [reading, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  let w := SCC G a b c
  change run (core G 1) w = Top G (sail (ray w) 0)
  rw [show sail (ray w) 0 = w from ?_]
  · exact (Book.enough w (F := run (core G 1)) (h := 3) (by simp [w, SCC])).symm
  simp [w, SCC, Detect.S, C, qnote]

private lemma product_two {p q : Cn} (hp : Low p) (hx : Low q) (ht : rulesPS p 0) :
    coeff 2 (p * q) = coeff 2 p + coeff 2 q := by
  rw [PowerSeries.coeff_mul]
  have he : coeff 1 p = 0 := ht 1 (fun ⟨i, hi⟩ => by omega)
  simp only [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  rw [hp, hx, he]
  ring

private lemma product_S (q : Option Axis) : adap T (q, true) x * adap T (q, false) x = 1 := by
  rw [mul_comm]
  cases q <;> dsimp only [adap, Bool.false_eq_true, if_false, if_true] <;> apply Program.pairs
include h

lemma counterpart (q : Option Axis) :
    coeff 2 (adap T (q, true) x) = -(coeff 2 (adap T (q, false) x)) := by
  have hp :=
    product_two (adap0 T x (q, true)) (adap0 _ _ _) (Z_even x h (q, true)) (q := adap T (q, false) x)
  rw [product_S, PowerSeries.coeff_one, if_neg (show (2 : ℕ) ≠ 0 from by omega)] at hp
  exact eq_neg_of_add_eq_zero_left hp.symm

lemma varied_S (a b c : G.ColorIndex) :
    M_ 3(x) (SCC G a b c) - M_ 3(y) (SCC G a b c) =
      (φC T x - φC T y + (Cx T x - Cx T y)) * (↑(LieColor a b c) : ℂ) := by
  let w := SCC G a b c
  have hx (z : ℝ) : coeff 2 ((w.map (fun u => adap T u.1.1 z)).prod) = Cx T z := by
    change coeff 2 (adap T gaugeC z * (adap T ghost z * (adap T ghost z * 1))) = _
    rw [mul_one, ← mul_assoc (adap T gaugeC z), product_S z none, one_mul]
    rfl
  unfold style
  rw [point₃ h x, point₃ h y, hx, hx, token_core]
  unfold φC
  ring

lemma varied_A (i : G.ColorIndex) (q : QP) :
    M_ 2(x) (AA G i q) - M_ 2(y) (AA G i q) = -(2 * (a(x) - a(y))) * (precision 1 1 (wave q) : ℂ) := by
  let w := AA G i q
  have hx (z : ℝ) : coeff 2 ((w.map (fun u => adap T u.1.1 z)).prod) = 2 * a(z) := by
    let A := adap T (Landau.gauge 1) z
    change coeff 2 (A * (A * 1)) = _
    rw [mul_one, product_two (adap0 ..) (adap0 ..) (Z_even z h _), two_mul]
    rfl
  unfold style
  rw [point₂ h x (core G), point₂ h y (core G), hx, hx,
    show run (core G 0) w = -(precision 1 1 (wave q) : ℂ) from ?_]
  ring
  change s₀ G [_, _] = _
  rw [rankTwo]
  simp [styleK, matchA, α₂, μ2]

lemma varied_U (i : G.ColorIndex) (q : QP) :
    M_ 2(x) (CU G i q) - M_ 2(y) (CU G i q) =
      (Cx T x - Cx T y - (a(x) - a(y))) * -(Complex.I * (wave q 0 : ℂ)) := by
  let w := CU G i q
  have hx (z : ℝ) : coeff 2 ((w.map (fun u => adap T u.1.1 z)).prod) = c(z) - a(z) := by
    change coeff 2 ((adap T ghost z) * (adap T (anti 0) z * 1)) = _
    rw [mul_one, product_two (adap0 ..) (adap0 ..) (Z_even z h _), counterpart h z (some 0),
      sub_eq_add_neg]
    rfl
  unfold style
  rw [point₂ h x, point₂ h y, hx, hx, show run (core G 0) w = -(Complex.I * (wave q 0 : ℂ)) from ?_]
  ring
  change s₀ G [_, _] = _
  rw [rankTwo]
  simp [styleK, matchA, α₂, μ2]
end YM.WilsonMS.BetaValue
