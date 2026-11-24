import YM.Integration.WilsonOlderFreshGraphDatedSalary
import YM.Integration.WilsonOriginalStarSceneRows

/-! A normalized column has its actual fresh amplitude at its booked
point, with all its path positions still included in the Roll salary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphPointWallet

open Function Filter Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink
open scoped Classical BigOperators Topology
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada

variable {G:Gauge} {n:Side} {Q d:ℕ} {σ:ℝ}

def point (y:Site n):Earn.Binder (Earn.Passport.point (fun _:Unit=>y)) (Stock.census Unit):=
  WilsonOriginalStarSceneRows.binder (fun _:Unit=>y) ()

lemma cost (T:WilsonOlderFreshGraphSlate.Copy G d Q σ) (y:Site n):
    T.cost (point y)=∑ j,T.fare j:=by
  simp [WilsonOlderFreshGraphSlate.Copy.cost,WilsonOlderFreshGraphArmada.gross,point,WilsonOriginalStarSceneRows.length]

theorem original (T:WilsonOlderFreshGraphSlate.Copy G d Q σ)(y:Site n){H:ℝ}
    (salary:(∑j,T.fare j) ≤ H) (Ω:ℝ) (hΩ:0<Ω):
    ∃c w:ℝ,0<c  ∧  c ≤ 1  ∧  c ≤ Ω⁻¹  ∧  0<w  ∧  w*T.cost (point y) ≤ c  ∧ 
      w⁻¹ ≤ max 1 Ω * (1+H):=by
  let c:ℝ:=(max 1 Ω)⁻¹
  have b0:0 < max 1 Ω:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have c0:0<c:=inv_pos.mpr b0
  have low:(0:ℝ) ≤ T.cost (point y):=by
    rw [cost]
    exact Finset.sum_nonneg (fun j _=>(tsum_nonneg (T.paid j).price.1).trans (T.paid j).price.2.2)
  obtain ⟨w,w0,paid,mass⟩:=WilsonOlderFreshGraphWallet.radius c c0 (T.cost (point y)) low
  refine ⟨c,w,c0,?_,?_,w0,paid,?_⟩
  · simpa [c] using (inv_anti₀ zero_lt_one (le_max_left 1 Ω))
  · exact inv_anti₀ hΩ (le_max_right 1 Ω)
  · rw [mass,cost]
    calc
      (1+∑j,T.fare j)/c = max 1 Ω*(1+∑j,T.fare j):=by simp [c,div_eq_mul_inv,mul_comm]
      _  ≤  _ :=mul_le_mul_of_nonneg_left (by linarith) b0.le
end YM.Integration.WilsonOlderFreshGraphPointWallet
end
