import YM.Integration.WilsonMeasuredOriginalCatalogueUnion
import YM.Integration.WilsonEmittedJoinedFares

/-! Cash for each issued child and every lag of the previously filed lower
word, before evaluation at the physical coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredJointCensusCash
open QuadraticLocal QuadraticLocal.Earn Marker WilsonMeasuredTransitionCatalogue
open scoped BigOperators Classical

variable {C V : Type} [Fintype C] [Fintype V] {D:ℕ} {J:Census Unit}
    (s:J.Mode) (w:C→Unit→ℝ) (w₀:V→Unit→ℝ) (b:C→ℝ) (b₀:V→ℝ) (r:ℝ) (c:V→ℕ→ℝ)

def radius : Names C V D → Unit→ℝ
  | .inl z=>w z
  | .inr (v,_)=>w₀ v

def cost : Names C V D → ℝ
  | .inl z=>b z
  | .inr (v,_)=>b₀ v

theorem split : WilsonEmittedJoinedFares.cash s (radius (D:=D) w w₀)
    (weight r c) (cost b b₀) =
    (∑z:C, |r| * ((Poly.toll (w z) s)⁻¹*b z)) +
      WilsonEmittedJoinedFares.cash s (fun i:V×Fin (D+1)=>w₀ i.1)
        (fun i:V×Fin (D+1)=>c i.1 i.2.val) (fun i:V×Fin (D+1)=>b₀ i.1) := by
  classical
  unfold WilsonEmittedJoinedFares.cash
  rw [Fintype.sum_sum_type]
  simp only [radius,cost,weight,abs_neg]

theorem original {x M:ℝ} (hx:1≤x)(hm:0≤M)
    (fresh:(∑z:C,|r| * ((Poly.toll (w z) s)⁻¹*b z))≤32*x^4*M)
    (old:WilsonEmittedJoinedFares.cash s (fun i:V×Fin (D+1)=>w₀ i.1)
      (fun i:V×Fin (D+1)=>c i.1 i.2.val) (fun i:V×Fin (D+1)=>b₀ i.1) ≤ 2*x^2*M) :
    WilsonEmittedJoinedFares.cash s (radius (D:=D) w w₀) (weight r c) (cost b b₀) ≤ 34*x^4*M := by
  rw [split]
  have growth:x^2 ≤ x^4:=pow_le_pow_right₀ hx (by decide)
  calc
    _ ≤ 32*x^4*M+2*x^2*M:=add_le_add fresh old
    _ ≤ 32*x^4*M+2*x^4*M:=by gcongr
    _ = _:=by ring

end YM.Integration.WilsonMeasuredJointCensusCash
end
