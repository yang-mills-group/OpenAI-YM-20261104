import YM.Integration.WilsonOriginalCompensatedRadius
import YM.QuadraticLocal.Class.Venture

/-! Two funded row families share a registered passport. Their signed rows remain
separate in the disjoint index sum. Each takes one half of the next Page wallet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCompensatedPortfolio
open Finset RG Marker Lattice QuadraticLocal QuadraticLocal.Earn PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums Push.PriceCompiler
open scoped Classical BigOperators

variable {V α ι ξ : Type} [DecidableEq V] {G:Gauge} {n:Side} {P:Passport n V} {R:Census V}
  (M:ι→Row P R G α) (N:ξ→Row P R G α)
  {w:V→ℝ} {t:V→ℕ} {σ f g:ℝ} {o h v:ℕ}

theorem gathered (left:Scene.Armada M w t σ f o h v)
    (right:Scene.Armada N w t σ g o h v) :
    Scene.Armada (Sum.elim M N) w t σ (f+g) o h v := by
  refine ⟨left.toMinistry,left.positive,?_,⟨?_,?_⟩,?_⟩
  · intro x
    let coin (i:ι⊕ξ):ℝ:=if (Sum.elim M N i).center=x then
      Poly.toll w (Sum.elim M N i).mode * (Sum.elim M N i).height σ else 0
    have l:SumBudget (coin ∘ Sum.inl) f:=left.suggests x
    have r:SumBudget (coin ∘ Sum.inr) g:=right.suggests x
    have sum:=l.2.1.hasSum.sum (f:=coin) r.2.1.hasSum
    refine ⟨?_,sum.summable,sum.tsum_eq.trans_le (add_le_add l.2.2 r.2.2)⟩
    intro i
    cases i with
    | inl i => exact l.1 i
    | inr i => exact r.1 i
  · exact Sum.rec (fun i=>left.purchases.spend i) (fun i=>right.purchases.spend i)
  · exact Sum.rec (fun i=>left.purchases.usable i) (fun i=>right.purchases.usable i)
  · exact Sum.rec (fun i=>left.honor i) (fun i=>right.honor i)

/-- Both inputs are the actual already contracted salaries on the common
passport. The second vote tests the full old and fresh union at every club. -/
theorem voters [Fintype V] {fine coarse vac:ℕ} (school:Syl.School vac)
    (step:StepStages fine coarse) (enough:AllOrder.Burn.horizon vac+2≤coarse)
    (old:Scene.Armada M w t σ f school.order school.pieces school.horizon)
    (fresh:Scene.Armada N w t σ g school.order school.pieces school.horizon)
    {Ω:ℝ} (first:f≤Ω⁻¹) (second:g≤Ω⁻¹) :
    Scene.Armada (Sum.elim M N) (Stoop.radius w 2) t σ
      ((2:ℝ)⁻¹*(f+g)) school.order school.pieces school.horizon ∧
    (2:ℝ)⁻¹*(f+g) ≤ Ω⁻¹ ∧
    Mentor.Cruise.Voter (Sum.elim M N) σ school.order
      (school.room step enough).count (school.room step enough).stage vac coarse := by
  have merged:=(gathered M N old fresh).stored (by norm_num : (1:ℝ)≤2)
  exact ⟨merged,by linarith,school.future step enough t (Sum.elim M N) merged⟩

end YM.Integration.WilsonOriginalCompensatedPortfolio
