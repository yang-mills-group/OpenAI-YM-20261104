import YM.Integration.WilsonThermometerPositionFilmParity
import YM.Comparison.RG02.Assembly.Shift

/-! A nonlinear curve with the same first two jets leaves the leading and next jet of a graded material socket fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmSocketJet
open Function Filter Finset Comparison.RG02.Assembly
open scoped Classical BigOperators Topology ContDiff
variable {E B:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]

private theorem size {k d:ℕ} (c:OrderedFinpartition k) (enough:d≤c.length) (below:k≤d+1) (i:Fin c.length):
    c.partSize i≤2 := by
  have sum : (∑j,c.partSize j)=k:=by
    have h : Fintype.card ((j:Fin c.length) × Fin (c.partSize j))=k:=by
      rw [Fintype.card_congr c.equivSigma,Fintype.card_fin]
    simpa only [Fintype.card_sigma,Fintype.card_fin] using h
  have split : (∑j,(c.partSize j-1))+c.length=k:=by
    calc
      _=(∑j:Fin c.length,((c.partSize j-1)+1)):=by simp [Finset.sum_add_distrib]
      _=∑j,c.partSize j:=by
        apply Finset.sum_congr rfl
        intro j _
        have pos:=c.partSize_pos j
        omega
      _=k:=sum
  have localBound:=Finset.single_le_sum (f:=fun t:Fin c.length=>c.partSize t-1)
    (fun t _=>Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem curve {d k:ℕ} (outer:E→B) (graded:GradeAt d outer) (below:k≤d+1)
    (f g:ℝ→E) (hf:ContDiffAt ℝ ω f 0) (hg:ContDiffAt ℝ ω g 0) (f0:f 0=0) (g0:g 0=0)
    (matching:∀i≤2,iteratedFDeriv ℝ i f 0=iteratedFDeriv ℝ i g 0) :
    iteratedFDeriv ℝ k (outer ∘ f) 0=iteratedFDeriv ℝ k (outer ∘ g) 0 := by
  have of₁:ContDiffAt ℝ ω outer (f 0):=f0.symm ▸ graded.smooth
  have of₂:ContDiffAt ℝ ω outer (g 0):=g0.symm ▸ graded.smooth
  rw [iteratedFDeriv_comp of₁ hf le_top,iteratedFDeriv_comp of₂ hg le_top,f0,g0]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c _
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries]
  by_cases hd:c.length<d
  · rw [graded.vanish _ hd]
    rfl
  · apply congrArg
    funext i
    rw [matching (c.partSize i) (size c (Nat.le_of_not_gt hd) below i)]

private theorem starts (f:ℝ→ℝ) (analytic:ContDiffAt ℝ ω f 0) (z:f 0=0) (h:HasDerivAt f 0 0) :
    GradeAt 2 f := by
  refine ⟨analytic,?_⟩
  intro j hj
  interval_cases j
  · apply ContinuousMultilinearMap.ext
    intro v
    rw [iteratedFDeriv_zero_apply,z]
    rfl
  · apply ContinuousMultilinearMap.ext
    intro v
    rw [iteratedFDeriv_one_apply,h.hasFDerivAt.fderiv]
    simp

end YM.Integration.WilsonThermometerPositionFilmSocketJet
