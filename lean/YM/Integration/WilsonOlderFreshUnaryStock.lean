import YM.Integration.WilsonOlderFreshUnaryVoter
import YM.Integration.WilsonOlderFreshGraphArmada

/-! An actual one-name gallery can be launched from its original unrestricted
salary. Shrinking the single input radius pays the authentic school bill on
every field, with an explicit reciprocal and the same source model. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshUnaryStock
open Lattice Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene Push WilsonOlderFreshGraphArmada
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{P:Passport n Unit}{R:Census Unit}{ι α:Type}
    (X:ι→Row P R G α)(w:Unit→ℝ)(d p seats h:ℕ)(σ b:ℝ)
    (earned:Armada X w (fun _=>d) σ b p seats h)

include earned in
theorem scaled {u:ℝ}(pos:0<u):
    Armada X (fun v=>u*w v) (fun _=>d) σ (u*b) p seats h:=by
  refine ⟨earned.toMinistry,fun v=>mul_pos pos (earned.positive v),?_,earned.purchases,earned.honor⟩
  intro y
  have root:=Local.sumBudget_mul_left (earned.suggests y) pos.le
  convert root using 1
  funext i
  by_cases found:(X i).center=y
  · simp [found,Poly.toll,full_mode (X i).binder,mul_assoc]
  · simp [found]

include earned in
theorem funded (B0:0≤b){Ω:ℝ}(gate:0<Ω):
    ∃(c a:ℝ),0<c ∧ c≤1 ∧ c≤Ω⁻¹ ∧ 0<a ∧ a⁻¹=max 1 Ω*(1+b) ∧
      Armada X (fun v=>a*w v) (fun _=>d) σ c p seats h:=by
  let κ:=max 1 Ω
  let c:=κ⁻¹
  let a:=(κ*(1+b))⁻¹
  have floor:1≤κ:=le_max_left .. 
  have strong:0<κ:=zero_lt_one.trans_le floor
  have outer:0<1+b:=by linarith
  have ap:0<a:=inv_pos.mpr (mul_pos strong outer)
  have size:a*b≤c:=by
    dsimp [a,c];rw [mul_inv_rev]
    calc
      _=κ⁻¹*((1+b)⁻¹*b):=by ring
      _≤κ⁻¹*1:=mul_le_mul_of_nonneg_left ((inv_mul_le_one₀ outer).mpr (by linarith)) (inv_nonneg.mpr strong.le)
      _=_:=mul_one _
  have actual:=scaled X w d p seats h σ b earned ap
  refine ⟨c,a,inv_pos.mpr strong,(inv_le_one₀ strong).mpr floor,
    inv_anti₀ gate (le_max_right ..),ap,by dsimp [a];rw [inv_inv],?_⟩
  refine ⟨actual.toMinistry,actual.positive,?_,actual.purchases,actual.honor⟩
  intro y
  have old:=actual.suggests y
  exact ⟨old.1,old.2.1,old.2.2.trans size⟩

end YM.Integration.WilsonOlderFreshUnaryStock
end
