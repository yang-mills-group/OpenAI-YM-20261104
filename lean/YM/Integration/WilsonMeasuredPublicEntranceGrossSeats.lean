import YM.Integration.WilsonMeasuredPublicEntrancePeerWindow
import YM.Integration.WilsonSeparatedPrefixCanonicalWallet

/-! The inverse of the actual mixed paid wallet uses the filed trial radius
once at each occupied name. All physical wages may have fixed polynomial
growth at their own reporting date. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceGrossSeats
open Function Filter Finset Lattice RG Wilson Marker QuadraticLocal
open WilsonThermometerMixedCollarSubpower WilsonSeparatedPrefixCanonicalWallet
open scoped Classical BigOperators Topology
variable {V:Type}[Fintype V][DecidableEq V]{J:Census V}

theorem original (t:ℕ)(C:ℝ)(cp:0≤C):
    ∀ᶠ H:ℝ in atTop,∀w₀ A B wY:V→ℝ,
    (∀v,0<w₀ v) → (∀v,0≤A v) → (∀v,0≤B v) → (∀v,0<wY v) →
    (∀v,(w₀ v)⁻¹≤H^t) → (∀v,A v+B v≤H^t) →
    (∀v,(wY v)⁻¹≤Real.exp (C*(1+Real.log H)*(scale H)^3)) →
    let w:=seat w₀ (fun v=>A v+(wY v)⁻¹) B
    ∀s:J.Mode,(Poly.toll (fun v=>w v^2) s)⁻¹≤Real.exp ((Real.log H)^2/128):=by
  let k:ℝ:=2+24*((Fintype.card V:ℝ)+1)
  let c:=k+t+C
  have kp:0≤k:=by dsimp [k];positivity
  have cn:0≤c:=by dsimp [c];positivity
  filter_upwards [WilsonMeasuredPublicEntrancePeerWindow.applied (J:=J) c cn (Fintype.card V)
    (fun s=>card_le_univ s.val),eventually_ge_atTop (1:ℝ)] with H room live w₀ A B wY wp ap bp yp first second trial w s
  let v:ℝ:=(1+Real.log H)*(scale H)^3
  have hp:0<H:=zero_lt_one.trans_le live
  have lg:0≤Real.log H:=Real.log_nonneg live
  have sc:1 ≤ scale H:=by unfold scale;linarith only [le_max_left 0 (Real.log (Real.log H))]
  have cube:1≤(scale H)^3:=one_le_pow₀ sc
  have one:1≤v:=(one_le_mul_of_one_le_of_one_le (by linarith) cube)
  have logv:Real.log H≤v:=(show Real.log H≤1+Real.log H by linarith).trans
    (le_mul_of_one_le_right (by linarith) cube)
  let e:=Real.exp ((t+C)*v)
  have ex:1≤e:=Real.one_le_exp (mul_nonneg (by positivity) (zero_le_one.trans one))
  have poly:H^t≤e:=by
    rw [←Real.exp_log hp,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left logv (Nat.cast_nonneg t)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right cp) (zero_le_one.trans one))
  have ty(v₀:V):(wY v₀)⁻¹≤e:=(trial v₀).trans (Real.exp_le_exp.mpr (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Nat.cast_nonneg t)) (zero_le_one.trans one)))
  obtain ⟨pos,_,exactFee,_,_⟩:=WilsonSeparatedPrefixCanonicalWallet.original w₀
    (fun v=>A v+(wY v)⁻¹) B wp (fun v=>add_nonneg (ap v) (inv_nonneg.mpr (yp v).le)) bp
  apply room w pos _ s
  intro i
  have debitCap:debit w₀ (fun v=>A v+(wY v)⁻¹) B i ≤ k*e:=by
    unfold debit
    have row:1+(A i+(wY i)⁻¹)+B i≤3*e:=by linarith only [ex,(second i).trans poly,ty i]
    have total:=mul_le_mul_of_nonneg_left row (show 0≤8*((Fintype.card V:ℝ)+1) by positivity)
    dsimp only [k]
    linarith only [total,(first i).trans poly,ex]
  have wsmall:w i≤1:=by
    change Real.sqrt ((debit w₀ (fun v=>A v+(wY v)⁻¹) B i)⁻¹)≤1
    apply Real.sqrt_le_one.mpr
    apply inv_le_one_of_one_le₀
    unfold debit
    have right:0≤8*((Fintype.card V:ℝ)+1)*(1+(A i+(wY i)⁻¹)+B i):=by
      have :=ap i;have :=bp i;have :=yp i;positivity
    linarith only [right,inv_nonneg.mpr (wp i).le]
  have wi:(w i)⁻¹≤(w i^2)⁻¹:=(inv_le_inv₀ (pos i) (sq_pos_of_pos (pos i))).mpr (by
    rw [pow_two];exact mul_le_of_le_one_right (pos i).le wsmall)
  calc (w i)⁻¹ ≤ debit w₀ (fun v=>A v+(wY v)⁻¹) B i := wi.trans_eq (exactFee i)
    _≤k*e:=debitCap
    _≤Real.exp (k*v)*e:=mul_le_mul_of_nonneg_right
      ((le_add_of_nonneg_right zero_le_one : k≤k+1).trans ((Real.add_one_le_exp k).trans
        (Real.exp_le_exp.mpr (le_mul_of_one_le_right kp one)))) (Real.exp_nonneg _)
    _=Real.exp (c*(1+Real.log H)*(scale H)^3):=by
      unfold e
      rw [←Real.exp_add]
      congr 1
      dsimp only [c,v]
      ring

end YM.Integration.WilsonMeasuredPublicEntranceGrossSeats
end
