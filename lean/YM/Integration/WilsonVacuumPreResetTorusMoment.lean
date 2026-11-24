import YM.Integration.WilsonVacuumPreResetTorusMomentBound

/-! Convergence of the complete rooted absolute tensor discrepancy with
any fixed polynomial displacement weight on the actual torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusMoment
open Filter Function Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank
open Matrix RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open WilsonVacuumPreResetTorusMomentBound
open scoped Classical BigOperators Topology
variable {α V:Type*}[Fintype α][NormedAddCommGroup V][NormedSpace ℝ V]{k:ℕ}

def term (P:raw α V (k+1))(d:ℕ)(x:Cloth α)(n:Side)(y:dock (Site n) α k):ℝ:=
  let row:=Fin.cons (foldUnder n x) y
  (1+soar (tor n) row:ℝ)^d*‖P n row‖

omit [Fintype α] in
private theorem pins (x:Cloth α)(y:dock Cover α k)(n:Side):
    Fin.cons (foldUnder n x) (slideC n y)=foldUnder n ∘ Fin.cons x y:=by
  funext a
  refine Fin.cases ?_ (fun i=>?_) a <;> rfl

theorem original (P:raw α V (k+1))(h:Yields P 0)(x:Cloth α)(d:ℕ):
    Tendsto (fun n=>∑y,term P d x n y) atTop (𝓝 0):=by
  classical
  obtain ⟨σ,A,warm,receipt⟩:=h.fees
  let C:=A*ceilPoly d (σ-σ/2)
  let bound (y:dock Cover α k):=C*sail (width (σ/2) k) terrain x.1 y
  let W (n:Side)(y:dock Cover α k):ℝ:=if housing x y n then term P d x n (slideC n y) else 0
  have total:Summable bound:=((train_pay (positive (half_pos warm) k) x.1 k).2.1).mul_left C
  have each (y:dock Cover α k):Tendsto (fun n=>W n y) atTop (𝓝 0):=by
    let row:Fin (k+1) → (Cover × α):=Fin.cons x y
    let price:=(1+soar terrain row:ℝ)^d
    have measure:=((h.point row).norm).const_mul price
    have limit:Tendsto (fun n=>price*‖P n (foldUnder n ∘ row)‖) atTop (𝓝 0):=by
      simpa only [dilute,Nat.succ_ne_zero,↓reduceIte,Pi.zero_apply,norm_zero,mul_zero] using measure
    apply limit.congr'
    filter_upwards [slide_end x.1 y,touched row] with n good located
    have home:housing x y n:=good
    simp only [W,if_pos home,term,pins]
    change _=(1+soar (tor n) (foldUnder n ∘ row):ℝ)^d*_
    rw [located]
  have dom:∀ᶠ n in atTop,∀y,‖W n y‖≤bound y:=by
    filter_upwards [receipt] with n hn y
    have row:Amber (tor n) σ A (P n):=by simpa only [dilute,Nat.succ_ne_zero,↓reduceIte] using hn
    by_cases good:housing x y n
    · have nonneg:0≤term P d x n (slideC n y):=by unfold term;positivity
      simp only [W,if_pos good,Real.norm_eq_abs,abs_of_nonneg nonneg]
      simpa [term,bound,C] using (at_root row warm d x y good)
    · simp only [W,if_neg good,norm_zero]
      exact mul_nonneg (mul_nonneg hn.1 (ceilPoly_pos ..).le) (sail_nn ..)
  have joined:=tendsto_tsum_of_dominated_convergence (bound:=bound) total each dom
  have sum:Tendsto (fun n=>∑' y,W n y) atTop (𝓝 0):=by simpa only [tsum_zero] using joined
  apply sum.congr'
  refine Eventually.of_forall fun n=>?_
  refine Eq.trans (tsum_congr fun y=>?_) (slip_rule x.1 (term P d x n))
  by_cases live:unfoldAt x.1 (slideC n y)=y <;> simp only [W,housing,live,↓reduceIte]

end YM.Integration.WilsonVacuumPreResetTorusMoment
