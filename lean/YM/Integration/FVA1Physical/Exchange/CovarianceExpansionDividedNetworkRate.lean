import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionLongEntryResidual

/-! Convert the exponentially localized network-set rate into the explicitly
requested clock and forced-allowance powers, including a polynomial physical
wallet. The entire binomial factor is bounded on the actual torus by its
geometric radius, independently of torus period and ultraviolet cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Push.AbsoluteSums.Animals
open scoped Classical
variable {n:Side}

/-- The cofinal joint-flag theorem supplies whatever fixed square-rate is
required. One physical power is claimed here even if more than one failed
site is available. The displayed geometric factor is independent of period. -/
theorem divided_window_rate (x κ A M:ℝ)(xp:1≤x)(kp:0≤κ)(small:κ≤1)(ap:0≤A)
    (d q h m r:ℕ)(many:0<m)(cap:M≤A*x^d)(a:Site n):
    M*Real.sqrt (((neighbors r a).card.choose m:ℕ)*
      (((x⁻¹)^(2*(d+q))*κ^(2*h))^m))≤
      A*Real.sqrt ((ballCost r).choose m:ℕ)*(x⁻¹)^q*κ^h:=by
  let z:=(x⁻¹)^(d+q)*κ^h
  have x0:0<x:=zero_lt_one.trans_le xp
  have ix:0≤x⁻¹:=inv_nonneg.mpr x0.le
  have ix1:x⁻¹≤1:=(inv_le_one₀ x0).mpr xp
  have zp:0≤z:=mul_nonneg (pow_nonneg ix _) (pow_nonneg kp _)
  have z1:z≤1:=by
    dsimp only [z]
    exact mul_le_one₀ (pow_le_one₀ ix ix1) (pow_nonneg kp _) (pow_le_one₀ kp small)
  have rate:(x⁻¹)^(2*(d+q))*κ^(2*h)=z^2:=by
    dsimp only [z]
    rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm (d+q) 2,Nat.mul_comm h 2]
  have drop:z^m≤z:=by
    obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero many.ne'
    rw [hk,pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ zp z1) zp).trans_eq (one_mul _)
  have scale:x^d*z=(x⁻¹)^q*κ^h:=by
    dsimp only [z]
    rw [pow_add,←mul_assoc,←mul_assoc,inv_pow,mul_inv_cancel₀ (pow_ne_zero _ x0.ne'),one_mul]
  have geom:Real.sqrt ((neighbors r a).card.choose m:ℕ)≤Real.sqrt ((ballCost r).choose m:ℕ):=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.choose_le_choose m (neighbors_card r a))
  rw [rate,pow_right_comm,Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq (pow_nonneg zp m)]
  calc M * (Real.sqrt ((neighbors r a).card.choose m:ℕ) * z^m)
        ≤(A*x^d)*(Real.sqrt ((ballCost r).choose m:ℕ)*z):=mul_le_mul cap
          (mul_le_mul geom drop (pow_nonneg zp _) (Real.sqrt_nonneg _))
          (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg zp _)) (mul_nonneg ap (pow_nonneg x0.le _))
       _=A*Real.sqrt ((ballCost r).choose m:ℕ)*(x^d*z):=by ring
       _=A*Real.sqrt ((ballCost r).choose m:ℕ)*(x⁻¹)^q*κ^h:=by rw [scale];ring

end YM.Integration.FVA1Physical.Exchange.RoseCut
