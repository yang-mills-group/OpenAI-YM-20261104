import YM.Integration.WilsonPositionProgramDisjointWallet

/-! Weighted finite-volume charges of all genuine squarefree ordinary integrands and their signed difference. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianMomentBank
open Finset Multi Marker Comparison.RG02.Cumulants Next.SectorChange Next.Rank
open WilsonPositionProgramDisjointWallet
open scoped BigOperators Classical
variable {I V:Type} [Fintype I][DecidableEq I][DecidableEq V] {R:Census V}

def ones (R:Census V): (parts R).Mode→ℂ:=fun _=>1
def number (R:Census V):ℕ:=Fintype.card (Hot R)
def words (R:Census V):ℝ:=WilsonPositionProgramDisjointWallet.stock (ones R)

omit [Fintype I] [DecidableEq I] in
theorem read (P:Hot R→Normal.poly I)(s:R.Mode)(z:I→ℝ):
    Cloud.paint z (Cloud.integrand P s)=table (ones R) (fun i=>Cloud.paint z (P i)) s:=by
  simp [Cloud.integrand,table,ones]

omit [DecidableEq I] in
theorem pointwise (w:V→ℝ)(hw:∀v,0<w v)(P Q:Hot R→Normal.poly I)(k:ℕ){B δ:ℝ}(hb:1≤B)(hd:0≤δ)
    (hp:∀i z,Poly.toll w i.val*‖Cloud.paint z (P i)‖≤B*(1+‖z‖)^k)
    (hq:∀i z,Poly.toll w i.val*‖Cloud.paint z (Q i)‖≤B*(1+‖z‖)^k)
    (fee:∀i z,Poly.toll w i.val*‖Cloud.paint z (P i-Q i)‖≤δ*(1+‖z‖)^k)(s:R.Mode)(z:I→ℝ):
    Poly.toll w s*‖Cloud.paint z (Cloud.integrand P s)‖ ≤
      (words R*B^(number R))*(1+‖z‖)^(k*number R) ∧
    Poly.toll w s*‖Cloud.paint z (Cloud.integrand P s-Cloud.integrand Q s)‖ ≤
      (δ*(words R*(number R:ℝ)*B^(number R)))*(1+‖z‖)^(k*(number R+1)):=by
  let t:=1+‖z‖
  have ht:1≤t:=by dsimp [t];linarith [norm_nonneg z]
  have hB:1≤B*t^k:=one_le_mul_of_one_le_of_one_le hb (one_le_pow₀ ht)
  have δpos:0≤δ*t^k:=mul_nonneg hd (pow_nonneg (zero_le_one.trans ht) _)
  have each(i:Hot R):Poly.toll w i.val*‖Cloud.paint z (P i)-Cloud.paint z (Q i)‖≤δ*t^k:=by
    rw [←map_sub];exact fee i z
  have raw:=common w hw (ones R) (fun i=>Cloud.paint z (P i)) (fun i=>Cloud.paint z (Q i)) s
    hB δpos (fun i=>hp i z) (fun i=>hq i z) each
  have cost:salary (ones R) s≤words R:=tariff (ones R) s
  have B0:=zero_le_one.trans hB
  constructor
  · rw [read]
    calc
      _≤words R*(B*t^k)^(number R):=raw.1.trans (mul_le_mul_of_nonneg_right cost (pow_nonneg B0 _))
      _ = _:=by rw [mul_pow,←pow_mul];ring
  · rw [map_sub,read,read]
    calc
      _≤words R*((number R:ℝ)*(δ*t^k)*(B*t^k)^(number R)):=
        raw.2.trans (mul_le_mul_of_nonneg_right cost (by positivity))
      _ = _:=by
        change _ = _*t^(k*(number R+1))
        rw [mul_pow,←pow_mul,Nat.mul_add,Nat.mul_one,pow_add]
        ring

end YM.Integration.WilsonPositionProgramGaussianMomentBank
end
