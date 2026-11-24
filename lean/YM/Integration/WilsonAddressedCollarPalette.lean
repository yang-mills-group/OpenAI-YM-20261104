import YM.Integration.WilsonAddressedCollarReturn
import YM.Integration.WilsonCloseCaptureCalendar

/-! Original paid address tickets, in the normalization of the physical reporter. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedCollarPalette
open Finset Filter Lattice Wilson RG Source Extra.Histories RG05Readout RG05Readout.Address
open RG05Readout.Native RG05Readout.Planes RG05Readout.Pulse WilsonLimitConstruction
open Trace.Pilot PhysicalNext.Repeat.Legato Bandage
open scoped Classical Topology
variable {G : Gauge} {C : Family G} {d : ℕ}

private theorem low_ticket (a : Mark C d) {e : ℕ} (lt : e < weights a) :
    Address.clear C d e (ticket a) = 0 := by
  obtain ⟨k,j⟩ := a
  funext l q
  by_cases letter : l = k
  · subst l
    by_cases index : q = j
    · subst q
      change (if weights (C:=C) ⟨k,j⟩ ≤ e then _ else 0) = 0
      rw [if_neg (Nat.not_le.mpr lt)]
    · simp [Address.clear, ticket, chunk_self, Size.axis, Pi.single_eq_of_ne index]
  · simp [Address.clear, ticket, chunk_miss _ letter]

private theorem whole {D : Rail C} {B : ℕ → ℕ → ℝ} {m b N p : ℕ}
    (h : C.Makes) (wallet : Awake D B b d) {H : Sight C d p} {U : Emblems C d}
    (paid : Spine D B h b p d N H U) (base : b ≤ m) {u : ℕ} (mu : m ≤ u) (uN : u ≤ N)
    (x : Palette C d) :
    bounty B d m * size ((finer U mu).symm x) ≤
      bounty B d u * (C.S.a m / C.S.a u)^d * size x := by
  induction u,mu using Nat.le_induction generalizing x with
  | base => rw [base_value,LinearEquiv.refl_symm,LinearEquiv.refl_apply,
                div_self (C.S.a_pos _).ne',one_pow,mul_one]
  | succ k mk ih =>
    let L : ℝ := (C.S.block k).val
    have Lpos : 0 < L := by unfold L; positivity
    rw [finer_next mk]
    apply (ih (k.le_succ.trans uN) (U k x)).trans
    have step := (Costume.earned (e:=0) h paid wallet (base.trans mk) uN).body x
    have one := (grows (B:=B) (d:=d) k).1
    have bill : size (U k x) ≤ productCost B d k * (L^d*size x) := by
      have scaled := step.trans (mul_le_mul_of_nonneg_left (size_tuned ..) (zero_le_one.trans one))
      exact scaled.trans (mul_le_mul_of_nonneg_right
        (le_trans (by linarith only [one]) (grows k).2.2.1)
        (mul_nonneg (pow_nonneg Lpos.le _) (size_ge _)))
    apply (mul_le_mul_of_nonneg_left bill (mul_nonneg (zero_le_one.trans (bounty_head _))
      (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _))).trans_eq
    have mesh : C.S.a m / C.S.a (k+1) = C.S.a m / C.S.a k * L := by
      rw [C.S.a_step]; unfold L; field_simp
    rw [bounty_up,mesh,mul_pow]
    ring

private theorem engineering {m u n : ℕ} (hn : n ≤ d) (z : Palette C d) (fee : ℝ)
    (paid : size z ≤ fee * (C.S.a m / C.S.a u)^(d-n)) :
    size (lightest C d m u • z) ≤ fee * (C.S.a u / C.S.a m)^n := by
  have invbill : (C.S.a u / C.S.a m)^d * (C.S.a m / C.S.a u)^(d-n) =
      (C.S.a u / C.S.a m)^n := by
    calc
      _ = (C.S.a u / C.S.a m)^(d-n + n) * (C.S.a m / C.S.a u)^(d-n) := by
        rw [Nat.sub_add_cancel hn]
      _ = _ := by
        rw [pow_add,mul_right_comm,←mul_pow,
          show C.S.a u / C.S.a m * (C.S.a m / C.S.a u) = 1 by
            field_simp [(C.S.a_pos m).ne', (C.S.a_pos u).ne'], one_pow,one_mul]
  rw [size_smul]
  change ‖((C.S.a u : ℂ)/(C.S.a m : ℂ))^d‖ * size z ≤ _
  rw [norm_pow,norm_div,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (C.S.a_pos u).le, Real.norm_of_nonneg (C.S.a_pos m).le]
  exact (mul_le_mul_of_nonneg_left paid
    (pow_nonneg (div_nonneg (C.S.a_pos u).le (C.S.a_pos m).le) _)).trans_eq
      (by rw [mul_left_comm,invbill])

theorem original {R : Run G} (P : WilsonCloseCaptureCalendar.Funding R)
    (d : ℕ) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ {u N : ℕ} (mu : m ≤ u) (uN : u ≤ N) (p : ℕ) (a : Mark R.family d),
      let U := P.basis d (N,p)
      let top := finer U uN (ticket a)
      ∃ low : Palette R.family d,
        let fine := (finer U (mu.trans uN)).symm (top-low)
        (low = 0 ∨ (0 < weights a ∧ Address.clear R.family d (weights a-1) low = low ∧
          Address.clear R.family d (weights a-1) fine = 0)) ∧
        size (lightest R.family d m u • fine) ≤
          Real.exp (ε*(R.family.S.scale u-R.family.S.scale m)) *
          (R.family.S.a u / R.family.S.a m)^(weights a) ∧
        ∀ φ : Body, fieldC R.family u N p d (Many.point U (ticket a) u N) φ =
          fieldC R.family m N p d (Many.point U
            (lightest R.family d m u • (fine + (finer U (mu.trans uN)).symm low)) m N) φ := by
  let w := P.rows.age d
  filter_upwards [eventually_ge_atTop (P.start d), tariff w ε positive,
    WilsonAddressedCollarReturn.returned R.makes w positive] with m base fees returns u N mu uN p a
  obtain ⟨H,spine⟩ := P.rows.paid (N,p) d ((base.trans mu).trans uN)
  by_cases first : weights a = 0
  · refine ⟨0,Or.inl rfl,?_,?_⟩
    · simp only [sub_zero,Many.sumwalk _ mu uN,LinearEquiv.symm_trans_apply,
        LinearEquiv.symm_apply_apply,first]
      apply engineering (Nat.zero_le d)
      rw [Nat.sub_zero]
      have all := whole R.makes w spine base mu uN (ticket a)
      rw [size_ticket,mul_one] at all
      apply (le_of_mul_le_mul_left (a := bounty P.allowance d m) ·
        (zero_lt_one.trans_le (bounty_head (B:=P.allowance) (d:=d) m)))
      have growth : bounty P.allowance d u ≤ bounty P.allowance d m *
          Real.exp (ε*(R.family.S.scale u-R.family.S.scale m)) := fees u mu
      exact all.trans ((mul_le_mul_of_nonneg_right growth
        (pow_nonneg (div_nonneg (R.family.S.a_pos m).le (R.family.S.a_pos u).le) d)).trans_eq
          (mul_assoc _ _ _))
    · intro φ
      simp only [sub_zero,map_zero,add_zero,Many.sumwalk _ mu uN,
        LinearEquiv.symm_trans_apply,LinearEquiv.symm_apply_apply]
      exact summit _ _ mu uN φ
  · have pos : 0 < weights a := Nat.pos_of_ne_zero first
    have cap := capped a
    have prior : weights a-1+1 = weights a := Nat.sub_add_cancel pos
    obtain ⟨low,lower,zero,bill,read⟩ := returns mu uN spine
      (e:=weights a-1) (by omega) (ticket a) (low_ticket a (by omega))
    refine ⟨low,Or.inr ⟨pos,lower,zero⟩,?_,read⟩
    rw [size_ticket,mul_one,prior] at bill
    exact engineering cap _ _ bill

theorem total {R : Run G} (P : WilsonCloseCaptureCalendar.Funding R)
    (d : ℕ) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ {u N : ℕ} (mu : m ≤ u) (_ : u ≤ N) (p : ℕ)
      (x : Palette R.family d),
      size (lightest R.family d m u • (finer (P.basis d (N,p)) mu).symm x) ≤
        Real.exp (ε*(R.family.S.scale u-R.family.S.scale m))*size x := by
  let w := P.rows.age d
  filter_upwards [eventually_ge_atTop (P.start d), tariff w ε positive]
    with m base fees u N mu uN p x
  obtain ⟨_,spine⟩ := P.rows.paid (N,p) d ((base.trans mu).trans uN)
  have all := whole R.makes w spine base mu uN x
  let fee := Real.exp (ε*(R.family.S.scale u-R.family.S.scale m))
  have growth : bounty P.allowance d u ≤ bounty P.allowance d m * fee := fees u mu
  have paid : size ((finer (P.basis d (N,p)) mu).symm x) ≤
      fee * size x * (R.family.S.a m / R.family.S.a u)^(d-0) := by
    rw [Nat.sub_zero]
    apply (le_of_mul_le_mul_left (a := bounty P.allowance d m) ·
      (zero_lt_one.trans_le (bounty_head (B:=P.allowance) (d:=d) m)))
    have factor := pow_nonneg (div_nonneg (R.family.S.a_pos m).le (R.family.S.a_pos u).le) d
    exact all.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right growth factor) (size_ge x)).trans_eq (by ring))
  simpa only [pow_zero,mul_one] using engineering (Nat.zero_le d) _ _ paid

end YM.Integration.WilsonAddressedCollarPalette
