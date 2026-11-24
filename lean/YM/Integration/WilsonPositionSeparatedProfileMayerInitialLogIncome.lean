import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogBill

/-! The total weighted size of independently filed Taylor coefficients up to a fixed order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogIncome
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open WilsonPositionSeparatedProfileMayerInitialLogBill
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Marker.Census V}

theorem sum {r} (x:Grade Γ r) (w:V→ℝ) (A:ℝ)
    (paid:∀i≤r,∀s:Γ.Mode,Poly.toll w s*‖(observe Γ r x i).part s‖≤A):
    entire w (render x)≤(r+1:ℝ)*(Fintype.card Γ.Mode:ℝ)*A:=by
  classical
  have ins:(render x).support⊆range (r+1):=by
    intro i im
    by_contra no
    have hn:¬i<r+1:=by simpa using no
    exact (Polynomial.mem_support_iff.mp im) (by simp [render,PowerSeries.coeff_trunc,hn])
  have total i (hi:i∈range (r+1)):
      Poly.price w ((render x).coeff i)≤∑_:Γ.Mode,A:=by
    rw [render_coeff]
    exact Finset.sum_le_sum fun s _=>paid i (by have:=Finset.mem_range.mp hi;omega) s
  rw [entire,Finset.sum_subset ins (fun i _ ni=>by
    rw [Polynomial.notMem_support_iff.mp ni];simp)]
  calc
    _≤∑i∈range (r+1),∑_:Γ.Mode,A:=Finset.sum_le_sum total
    _=(r+1:ℝ)*(Fintype.card Γ.Mode:ℝ)*A:=by simp;ring

theorem value {r} (x:Grade Γ r) (w:V→ℝ) (hw:∀v,0<w v) (g:ℂ) (hg:‖g‖≤1):
    Poly.price w (Order.value g x)≤entire w (render x):=by
  classical
  rw [value_render,formula_sum,entire]
  apply (Poly.batch hw _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Poly.adapted,norm_pow]
  exact mul_le_of_le_one_left (Poly.nonnegative hw _) (pow_le_one₀ (norm_nonneg g) hg)

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogIncome
