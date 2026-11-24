import YM.Integration.WilsonReporterWeightedCourt

/-! Cancel the actual scaled mark and the one physical Ship divisor in the
same real monitor. The pre-election uses only the two active degrees. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedRankPrice
open Next.Rank.Atlas Lattice Wilson RG Next.Rank Next.Rank.Perch Tapes
open WilsonPhysicalThermalWickStretched (rates)
open scoped BigOperators
variable {G:Gauge}

def offsets (gap : ℕ) (i : Fin 2) : ℝ := if i=1 then gap else 0

theorem heats (g : ℕ) (s : ℝ) :
    WilsonReporterWeightedMarket.radius (offsets g) s=rates ((bill 1 s)^g) := by
  funext i
  by_cases e : i=1
  · simp [WilsonReporterWeightedMarket.radius,offsets,rates,e,bill,←Real.exp_nat_mul,mul_comm]
  · simp [WilsonReporterWeightedMarket.radius,offsets,rates,e,bill]

theorem purse {d D g:ℕ} (p:Tapes.Panel D) (small : d<D) (slots:g≤D) (j):
    p.arc*d+d+2+g≤(p.bag j).credit := by
  apply le_trans _ (p.loose j)
  have ha : D+6≤p.arc := p.huge
  have h : (d:ℝ)+1≤D := by exact_mod_cast small
  have h' : (g:ℝ)≤D := by exact_mod_cast slots
  have hz : 0≤p.arc := by linarith only [ha,Nat.cast_nonneg (α:=ℝ) D]
  nlinarith only [mul_le_mul_of_nonneg_left h hz,h,h',ha]

theorem gains (a:Levels G) (u k gap:ℕ) (A x:ℝ)
    (h:(∏ i, rates ((bill 1 (clim a k))^gap) i)*x ≤ A*Ship.budget a u k) :
    (a.clock.monitor k)^((gap:ℝ)+1/(16*u))*x≤A := by
  let P := a.clock.monitor k
  have hp : 0<P := Real.exp_pos _
  have hi : 0≤P^(1/(16*(u:ℝ))) := (Real.rpow_pos_of_pos hp _).le
  have hc : P^(1/(16*(u:ℝ)))*Ship.budget a u k=1 := by
    rw [Real.rpow_def_of_pos hp,Ship.budget,Ship.pot,←Real.exp_add]
    change Real.exp (Real.log P * (1/(16*(u:ℝ))) + -(Real.log P/(16*(u:ℝ))))=1
    rw [show Real.log P * (1/(16*(u:ℝ))) + -(Real.log P/(16*(u:ℝ)))=0 by ring,Real.exp_zero]
  rw [Fin.prod_univ_two] at h
  simp only [rates,Fin.zero_ne_one,if_false,if_pos,one_mul,←Atlas.fire_bill] at h
  change P^((gap:ℝ)+1/(16*u))*x≤A
  rw [Real.rpow_add hp,Real.rpow_natCast]
  calc P^gap*P^(1/(16*(u:ℝ)))*x = P^(1/(16*(u:ℝ)))*(P^gap*x) := by ring
       _ ≤ P^(1/(16*(u:ℝ)))*(A*Ship.budget a u k) := mul_le_mul_of_nonneg_left h hi
       _ = A := by rw [←mul_left_comm A,hc,mul_one]

end YM.Integration.WilsonReporterWeightedRankPrice
