import YM.Integration.WilsonOriginalPaidWalkCover
import YM.Integration.WilsonOriginalCenteredSeamSalary

/-! On the unchanged numerical covered field each row can use its own original paid walks. -/
noncomputable section
namespace YM.Integration.WilsonOriginalCoherentCoveredFields
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder.Floe Comparison.RG02
open FVA1Physical FVA1Physical.TwoReset Multi WilsonOriginalPaidWalkCover
open scoped BigOperators Classical
variable {G:Gauge} {n N:Side} {V ι α:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
  (h:n.val∣N.val) (M:ι→Row o J G α) (w:V→ℕ) (ink:ι→ℂ) (L:Layout G) (T:Finset Age)

def charged (p:Fin (Pages n N)) (s:Hot J) (g:ℝ) (U:Config G N) : ℂ :=
  ∑' z:ι,if (M z).mode=s.val then ink z * Complex.ofReal
    (Loan.letter (row h (M z) p).lamp (row h (M z) p).atom (row h (M z) p).center g U) else 0

theorem on_page (p:Fin (Pages n N)) (s:Hot J) (g:ℝ) (U:Config G N) :
    (Air.craft (fun z:ι=>TwoReset.copy h (M z) p) ink w L T).mark s g U=
      charged h M ink p s g U := by
  unfold charged
  simp only [Air.craft,QuadraticLocal.Fk.grant,Air.sums,ScatterR.familyAt,ScatterR.actor]
  apply tsum_congr
  intro z
  rw [WilsonOriginalPaidWalkCover.letter]
  simp only [Row.mode, TwoReset.copy]

theorem original (s:Hot J) (g:ℝ) (U:Config G N) :
    (TwoReset.copyColor h M w ink L T).mark s g U=∑p:Fin (Pages n N),charged h M ink p s g U := by
  simp only [TwoReset.copyColor,Finset.sum_apply]
  exact Finset.sum_congr rfl fun p _=>on_page h M w ink L T p s g U

theorem pieces {B:Type} [Fintype B] [DecidableEq B] (modes:B→Hot J) (g:ℝ) (U:Config G N) :
    (∏v:B,(TwoReset.copyColor h M w ink L T).mark (modes v) g U)=
      ∑p:B→Fin (Pages n N), ∏v:B,charged h M ink (p v) (modes v) g U := by
  rw [WilsonOriginalCarriedDeckForms.occupied h M w ink L T modes g U]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.prod_congr rfl
  intro v _
  exact on_page h M w ink L T (p v) (modes v) g U

end YM.Integration.WilsonOriginalCoherentCoveredFields
