import YM.Integration.WilsonOriginalCoherentCoveredFields
import YM.Integration.WilsonOriginalCoherentCoverSalary

/-! Resolve the complete signed covered field by the distinct actual lifts of its named owners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNamedRelativeRows
open Function Finset Lattice RG Wilson Marker Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn
open AllOrder.Floe Comparison.RG02 FVA1Physical TwoReset Multi
open WilsonOriginalPaidWalkCover
open scoped BigOperators Classical
variable {G:Gauge} {n N:Side} {V ι α:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
  (h:n.val∣N.val) (M:ι→Row o J G α) (grades:V→ℕ) (ink:ι→ℂ) (L:Layout G) (T:Finset Age)

def assigned (s:Finset V) (z:ι) (p:Fin (Pages n N)) : s→Fin (Pages n N) :=
  fun v=>index h (M z) p v.val

def part (p:Fin (Pages n N)) (s:Hot J) (u:s.val.val→Fin (Pages n N)) (g:ℝ) (U:Config G N) : ℂ :=
  ∑' z:ι,if (M z).mode=s.val ∧ assigned h M s.val.val z p=u then ink z * Complex.ofReal
    (Loan.letter (row h (M z) p).lamp (row h (M z) p).atom (row h (M z) p).center g U) else 0

theorem original {a:ℝ} {k:ℕ} (staff:Air.Staff M ink grades a k)
    (p:Fin (Pages n N)) (s:Hot J) (g:ℝ) (U:Config G N) :
    (Air.craft (fun z:ι=>TwoReset.copy h (M z) p) ink grades L T).mark s g U=
      ∑u:s.val.val→Fin (Pages n N),part h M ink p s u g U := by
  rw [WilsonOriginalCoherentCoveredFields.on_page]
  unfold WilsonOriginalCoherentCoveredFields.charged part
  let draw (z:ι):=ink z*Complex.ofReal
    (Loan.letter (row h (M z) p).lamp (row h (M z) p).atom (row h (M z) p).center g U)
  have pay (u:s.val.val→Fin (Pages n N)):Summable (fun z:ι=>
      if (M z).mode=s.val ∧ assigned h M s.val.val z p=u then draw z else 0):=by
    have q:=Air.usable_all (fun z:ι=>TwoReset.copy h (M z) p) ink grades (copy_staff h M grades ink staff p) U g
      (fun z:ι=>(M z).mode=s.val ∧ assigned h M s.val.val z p=u)
    simpa only [draw,WilsonOriginalPaidWalkCover.letter,ScatterR.familyAt] using q
  rw [←Summable.tsum_finsetSum (fun u _=>pay u)]
  apply tsum_congr
  intro z
  by_cases yes:(M z).mode=s.val
  · simp [yes,draw]
  · simp [yes]

theorem covered {a:ℝ} {k:ℕ} (staff:Air.Staff M ink grades a k)
    (s:Hot J) (g:ℝ) (U:Config G N) :
    (TwoReset.copyColor h M grades ink L T).mark s g U=
      ∑p:Fin (Pages n N),∑u:s.val.val→Fin (Pages n N),part h M ink p s u g U := by
  simp only [TwoReset.copyColor,Finset.sum_apply]
  exact Finset.sum_congr rfl fun p _=>original h M grades ink L T staff p s g U

theorem salary {w:V→ℝ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (σ0:0≤σ)
    (x:Site N) (t:α) (s:Finset V) (angular:Finset (Site N)) :
    SumBudget (fun z : Σ (_:Σ _:ι,Fin (Pages n N)),(s→Fin (Pages n N)) =>
      if assigned h M s z.1.1 z.1.2=z.2 then
        WilsonOriginalCoherentCoverSalary.amount h M w σ x t s angular z.1.1 z.1.2 else 0) C := by
  have funds:=WilsonOriginalCoherentCoverSalary.original h M stock σ0 x t s angular
  apply Push.Local.sumBudget_sigma (a:=fun z=>WilsonOriginalCoherentCoverSalary.amount h M w σ x t s angular z.1 z.2)
  · intro z
    apply budget_finite
    · intro u
      split
      · exact funds.1 z
      · exact le_rfl
    · simp
  · exact funds

end YM.Integration.WilsonOriginalNamedRelativeRows
