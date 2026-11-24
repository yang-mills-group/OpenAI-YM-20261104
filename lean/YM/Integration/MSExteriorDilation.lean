import YM.FVA2.NewTime

/-! Dilation of the full independent MS exterior residual, including the finite
physical-output projection and the perturbative convolution. The final bound
uses a uniform far estimate at the running subtraction scale. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.MSExteriorDilation
open Function Set Filter Finset Real MS MS.Land MS.Rake MS.Menus MS.Tone
open scoped BigOperators Topology Classical

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {Q : Booked B}
variable {n m H : ℕ}

abbrev weight (R : Fin n → Label B) : ℕ := ∑ j, (R j).h

abbrev moment (M : MS_Data G Q) (R : Fin n → Label B) (μ : ℝ)
    (z : Fin n → QP) (k : ℕ) : ℂ := Dial.tour M R μ z univ k

abbrev stretch (s : ℝ) (x : Fin n → QP) : Fin n → QP := fun j => exp s • x j

def power (w s : ℝ) : ℂ := (exp (w*s) : ℝ)

theorem power_add (a b s : ℝ) : power (a+b) s = power a s * power b s := by
  simp [power,add_mul,Real.exp_add]

theorem scales (M : MS_Data G Q) (R : Fin n → Label B) (μ s : ℝ)
    (x : Fin n → QP) (hx : Injective x) (k : ℕ) :
    moment M R μ x k = power (weight R) s * moment M R (μ-s) (stretch s x) k := by
  have h := FVA2.Waves.tour_time M R hx k (μ-s) s univ
  have hτ : MS.Port.τ (-(weight R : ℤ)) s = power (-(weight R : ℝ)) s := by
    unfold MS.Port.τ power
    rw [zpow_neg,zpow_natCast,neg_mul,Real.exp_neg,Real.exp_nat_mul]
  change moment M R (μ-s) (stretch s x) k =
    MS.Port.τ (-(weight R : ℤ)) s * moment M R (μ-s+s) x k at h
  rw [hτ,sub_add_cancel] at h
  rw [h,←mul_assoc,←power_add]
  simp [power]

abbrev centered (a : Glyph B H) (L : Fin m → Label B) : Fin (1+m) → Label B :=
  Fin.append (fun _ : Fin 1 => (⟨a.size,a.2⟩ : Label B)) L

theorem append_weight (R : Fin n → Label B) (L : Fin m → Label B) :
    weight (Fin.append R L) = weight R + weight L := by simp [weight,Fin.sum_univ_add]

theorem center_weight (a : Glyph B H) (L : Fin m → Label B) :
    weight (centered a L) = a.size + weight L := by rw [centered,append_weight]; simp [weight]

variable (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)

/-- A coefficient table at the fixed inner positions, indexed by the running log μ. -/
abbrev Table (B : MS.Local.Physical.Deck G) (H : ℕ) := Glyph B H → ℕ → ℝ → ℂ

def far (C : Table B H) (v : ℝ) (q : Fin (n+m) → QP) (u : Fin (1+m) → QP) (k : ℕ) : ℂ :=
  moment M (Fin.append R L) v q k - ∑ a : Glyph B H,
    ∑ p ∈ HasAntidiagonal.antidiagonal k, C a p.1 v * moment M (centered a L) v u p.2

def near (C : Table B H) (μ s : ℝ) (q : Fin (n+m) → QP) (u : Fin (1+m) → QP) (k : ℕ) : ℂ :=
  moment M (Fin.append R L) μ q k - ∑ a : Glyph B H, ∑ p ∈ HasAntidiagonal.antidiagonal k,
    power ((weight R : ℝ)-a.size) s * C a p.1 (μ-s) * moment M (centered a L) μ u p.2

/-- Generic separated points permit both the receding and contracted geometries,
with an arbitrary common origin via the genuine original translation law. -/
theorem scale_residual (C : Table B H) (μ s : ℝ) (q : Fin (n+m) → QP) (hq : Injective q)
    (u : Fin (1+m) → QP) (hu : Injective u) (k : ℕ) :
    near M R L C μ s q u k = power ((weight R : ℝ)+weight L) s *
      far M R L C (μ-s) (stretch s q) (stretch s u) k := by
  unfold near far
  rw [mul_sub,scales M (Fin.append R L) μ s q hq k,append_weight,Nat.cast_add]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : power ((weight R : ℝ)-a.size) s * power ((a.size : ℝ)+weight L) s =
      power ((weight R : ℝ)+weight L) s := by
    rw [←power_add]
    congr 1; ring
  rw [scales M (centered a L) μ s u hu p.2,center_weight,Nat.cast_add,←e]
  ring

/-- Along the actual running scale v=μ−s the original bound spends at most
one extra factor of the logarithmic polynomial and preserves the full power. -/
theorem budget (μ s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    ((1+|μ-s|)*(1+s))^k ≤ (1+|μ|)^k*(1+|s|)^(2*k) := by
  rw [abs_of_nonneg hs,pow_mul,←mul_pow]
  have hab := (abs_sub μ s).trans_eq (by rw [abs_of_nonneg hs])
  apply pow_le_pow_left₀ (by positivity)
  have hh : 1+|μ-s| ≤ (1+|μ|)*(1+s) := by nlinarith [mul_nonneg (abs_nonneg μ) hs]
  calc _ ≤ ((1+|μ|)*(1+s))*(1+s) := mul_le_mul_of_nonneg_right hh (by positivity)
       _ = _ := by ring

variable {I : Type} (C : I → Table B H) (q : ℝ → I → Fin (n+m) → QP)
    (u : I → Fin (1+m) → QP)

/-- All finite tuples and every index in a compact support use the same eventual
scale and constants whenever the genuine far estimate does. -/
theorem short_of_far (μ : ℝ) (k : ℕ) (hq : ∀ᶠ s : ℝ in atTop, ∀ i, Injective (q s i))
    (hu : ∀ i, Injective (u i)) {K : ℝ} (hK : 0≤K) (j : ℕ)
    (hfar : ∀ᶠ s : ℝ in atTop, ∀ i v,
      ‖far M R L (C i) v (stretch s (q s i)) (stretch s (u i)) k‖ ≤
        K * (((1+|v|)*(1+s))^j * exp (-((H:ℝ)+1+weight L)*s))) :
    ∀ᶠ s : ℝ in atTop, ∀ i,
      ‖near M R L (C i) μ s (q s i) (u i) k‖ ≤
        (K*(1+|μ|)^j) * (exp (((weight R : ℝ)-H-1)*s) * (1+|s|)^(2*j)) := by
  filter_upwards [eventually_ge_atTop (0:ℝ),hq,hfar] with s hs hsep h i
  rw [scale_residual M R L (C i) μ s _ (hsep i) _ (hu i) k,norm_mul,power,
    Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  refine (mul_le_mul_of_nonneg_left (h i (μ-s)) (Real.exp_pos _).le).trans ?_
  have hlog := budget μ s hs j
  calc
    _ ≤ exp (((weight R:ℝ)+weight L)*s) *
      (K*((1+|μ|)^j*(1+|s|)^(2*j)*exp (-((H:ℝ)+1+weight L)*s))) := by gcongr
    _ = (K*(1+|μ|)^j)*(exp (((weight R:ℝ)-H-1)*s)*(1+|s|)^(2*j)) := by
      have hpow : exp (((weight R:ℝ)+weight L)*s) * exp (-((H:ℝ)+1+weight L)*s) =
          exp (((weight R:ℝ)-H-1)*s) := by rw [←Real.exp_add]; congr 1; ring
      rw [←hpow]
      ring

/-- The inner configuration contracts by exp(-s). The exterior stays fixed. -/
abbrev contracted (s : ℝ) (x : Fin n → QP) (y : Fin m → QP) := Fin.append (stretch (-s) x) y

/-- The inner configuration stays fixed. The exterior recedes by exp(s). -/
abbrev receding (s : ℝ) (x : Fin n → QP) (y : Fin m → QP) := Fin.append x (stretch s y)

abbrev origin (y : Fin m → QP) := Fin.append (fun _ : Fin 1 => (0 : QP)) y

theorem position (s : ℝ) (x : Fin n → QP) (y : Fin m → QP) :
    stretch s (contracted s x y) = receding s x y := by
  funext i
  induction i using Fin.addCases with
  | left j => simp [stretch,contracted,receding,smul_smul,← Real.exp_add]
  | right j => simp [stretch,contracted,receding]

theorem anchored (s : ℝ) (y : Fin m → QP) : stretch s (origin y) = origin (stretch s y) := by
  funext i
  induction i using Fin.addCases <;> simp [stretch,origin]

theorem on_exterior (C : Table B H) (μ s : ℝ) (x : Fin n → QP) (y : Fin m → QP)
    (hs : Injective (contracted s x y)) (hy : Injective (origin y)) (k : ℕ) :
    near M R L C μ s (contracted s x y) (origin y) k = power ((weight R : ℝ)+weight L) s *
      far M R L C (μ-s) (receding s x y) (origin (stretch s y)) k := by
  rw [scale_residual M R L C μ s _ hs _ hy k,position,anchored]

theorem all_exteriors (C : I → Table B H) (x : I → Fin n → QP) (y : I → Fin m → QP)
    (μ : ℝ) (k : ℕ) (hx : ∀ᶠ s : ℝ in atTop, ∀ i, Injective (contracted s (x i) (y i)))
    (hy : ∀ i, Injective (origin (y i))) {K : ℝ} (hK : 0≤K) (j : ℕ)
    (hf : ∀ᶠ s : ℝ in atTop, ∀ i v,
      ‖far M R L (C i) v (receding s (x i) (y i)) (origin (stretch s (y i))) k‖ ≤
        K * (((1+|v|)*(1+s))^j * exp (-((H:ℝ)+1+weight L)*s))) :
    ∀ᶠ s : ℝ in atTop, ∀ i,
      ‖near M R L (C i) μ s (contracted s (x i) (y i)) (origin (y i)) k‖ ≤
        (K*(1+|μ|)^j) * (exp (((weight R : ℝ)-H-1)*s) * (1+|s|)^(2*j)) := by
  apply short_of_far M R L C (fun s i => contracted s (x i) (y i)) (fun i => origin (y i)) μ k hx hy hK j
  simpa only [position,anchored] using hf

end YM.Integration.MSExteriorDilation
