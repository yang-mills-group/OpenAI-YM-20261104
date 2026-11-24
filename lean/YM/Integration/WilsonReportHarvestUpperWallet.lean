import YM.Integration.WilsonReportHarvestResidentWallet

/-! Source-radius change on the original dated wallet when the true ultraviolet column has an engineering charge. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestUpperWallet
open Finset Filter Lattice RG Wilson Marker Extra.Histories RG05Readout.Many
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}

private theorem shifted (C:Family G){m j:ℕ}(mj:m ≤ j)(d k:ℕ){Q Z:ℝ}:
    envelope C m d k (Q/Z) j=Z*envelope C m d k Q j:=by
  let x:=C.path.levels.clock.hatBeta j
  let f:=RG05Readout.Address.stringCost C mj
  have width (q:ℝ):envelope C m d k q j=(x^k*(q*f))⁻¹:=by
    unfold envelope west
    rw [rust_above mj,one_mul];unfold markWidth
    rw [total_upper mj,mul_inv_rev,div_eq_mul_inv,mul_comm]
  rw [width,width]
  simp only [mul_inv_rev,div_eq_mul_inv,inv_inv]
  ring

theorem weights (C:Family G)(simple:G.Simple)(k h L:ℕ):
    ∀ᶠm:ℕ in atTop,∀j:ℕ,m ≤ j → ∀d:ℕ,∀{V:Type}[DecidableEq V]{J:Census V}
      (Q:V → ℝ)(Z:ℝ),1 ≤ Z → (∀v,0<Q v) → (∀v,Q v ≤ (C.path.levels.clock.hatBeta m)^h*Z) →
      ∀s:J.Mode,s.val.card ≤ L →
      1 ≤ Z^L*((C.path.levels.clock.hatBeta j)^((k+h)*L)*Real.exp ((L:ℝ)*(C.S.scale j-C.S.scale m)))*
        Poly.toll (fun v=>envelope C m d k (Q v) j) s:=by
  filter_upwards [WilsonReportHarvestResidentWallet.weights C simple k h L] with m earned j mj d V inst J Q Z z1 positive cap s many
  let w:=fun v=>envelope C m d k (Q v) j
  have zp:0<Z:=zero_lt_one.trans_le z1
  have wp(v):0<w v:=by
    unfold w envelope west
    rw [rust_above mj,one_mul];exact grantw (totalpos (positive v) j)
  have bill:=earned j mj d (fun v=>Q v/Z) (fun v=>div_pos (positive v) zp)
    (fun v=>(div_le_iff₀ zp).mpr (cap v)) s many
  have shift:Poly.toll (fun v=>envelope C m d k (Q v/Z) j) s=Z^s.val.card*Poly.toll w s:=by
    unfold Poly.toll
    simp only [shifted C mj d k,Finset.prod_mul_distrib,Finset.prod_const,w]
  rw [shift] at bill
  let M:=(C.path.levels.clock.hatBeta j)^((k+h)*L)*Real.exp ((L:ℝ)*(C.S.scale j-C.S.scale m))
  have mp:0 ≤ M:=mul_nonneg (pow_nonneg (zero_lt_one.trans (C.path.levels.fits.delayed j)).le _) (Real.exp_pos _).le
  calc
    1 ≤ M*(Z^s.val.card*Poly.toll w s):=bill
    _ = Z^s.val.card*(M*Poly.toll w s):=by ring
    _ ≤ Z^L*(M*Poly.toll w s):=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ z1 many) (mul_nonneg mp (Poly.worth wp s).le)
    _ = _:=by dsimp only [M,w];ring

end YM.Integration.WilsonReportHarvestUpperWallet
