import YM.Integration.WilsonIndependentMatchedCoverSum
/-! Each first connection spends only the requested stable fraction on the actual optical interval. The residual positive exponent determines the finite geometric tariff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedShellSeries
open Finset Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonOriginalPublicPlantedFirstJoinScale
open private tape from YM.Integration.WilsonOriginalPublicPlantedStableCredit
open scoped BigOperators Topology Classical

def wage (a H ζ:ℝ):ℝ:=(1-(2:ℝ)^(-(a-H-ζ)))⁻¹

theorem positive {a H ζ:ℝ}(h:H+ζ<a):0<wage a H ζ:=by
  have slope:0<a-H-ζ:=by linarith
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr slope)))

theorem pay (S:Schedule)(m n:ℕ)(δ a H t ζ:ℝ)(hδ:0<δ)(upper:δ≤radius S m n)
    (released:ζ≤t)(clear:H+ζ<a):
    ∑i∈range n,(radius S m i)^(a-H)*(δ/radius S m i)^t ≤ wage a H ζ*δ^ζ:=by
  let γ:=a-H-ζ
  let q:ℝ:=(2:ℝ)^(-γ)
  have slope:0<γ:=by dsimp [γ];linarith
  have qp:0<q:=Real.rpow_pos_of_pos (by norm_num) _
  have cool:q<1:=Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr slope)
  have each (i:ℕ)(hi:i<n):(radius S m i)^(a-H)*(δ/radius S m i)^t≤δ^ζ*q^i:=by
    have radiusPos:=WilsonOriginalPublicPlantedFirstJoinScale.positive S m i
    have last:radius S m n≤radius S m i:=by
      simp only [WilsonIndependentMatchedCoverSum.spacing]
      exact div_le_div_of_nonneg_right (S.strictAnti.antitone (Nat.add_le_add_left hi.le m)) (S.a_pos m).le
    have shrink:δ/radius S m i≤1:=(div_le_one radiusPos).mpr (upper.trans last)
    have saved:=Real.rpow_le_rpow_of_exponent_ge (div_pos hδ radiusPos) shrink released
    have roof:(i:ℝ)*Real.log 2≤S.scale (m+i)-S.scale m:=
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by norm_num:(2:ℝ)≤3))
        (Nat.cast_nonneg i)).trans (tape S m i)
    have fees:Real.exp (-(S.scale (m+i)-S.scale m)*γ)≤q^i:=by
      rw [←Real.exp_log (pow_pos qp i),Real.log_pow]
      change _≤Real.exp ((i:ℝ)*Real.log ((2:ℝ)^(-γ)))
      rw [Real.log_rpow (by norm_num:(0:ℝ)<2)]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right roof slope.le]
    calc
      _≤(radius S m i)^(a-H)*(δ/radius S m i)^ζ:=
        mul_le_mul_of_nonneg_left saved (Real.rpow_nonneg radiusPos.le _)
      _=δ^ζ*Real.exp (-(S.scale (m+i)-S.scale m)*γ):=by
        rw [Real.rpow_def_of_pos radiusPos,Real.rpow_def_of_pos (div_pos hδ radiusPos),
          Real.rpow_def_of_pos hδ,Real.log_div hδ.ne' radiusPos.ne']
        dsimp only [radius]
        simp only [Real.log_exp,←Real.exp_add]
        congr 1
        dsimp only [γ]
        ring
      _≤_:=mul_le_mul_of_nonneg_left fees (Real.rpow_nonneg hδ.le ζ)
  have summable:=summable_geometric_of_lt_one qp.le cool
  have maxFee:(∑i∈range n,q^i)≤(1-q)⁻¹:=(summable.sum_le_tsum _ (fun i _=>pow_nonneg qp.le i)).trans_eq
    (tsum_geometric_of_lt_one qp.le cool)
  calc
    _≤∑i∈range n,δ^ζ*q^i:=sum_le_sum fun i hi=>each i (mem_range.mp hi)
    _=δ^ζ*(∑i∈range n,q^i):=by rw [mul_sum]
    _≤_:=by simpa only [wage,q,γ,mul_comm (δ^ζ)] using mul_le_mul_of_nonneg_left maxFee (Real.rpow_nonneg hδ.le ζ)
end YM.Integration.WilsonIndependentConditionedShellSeries
