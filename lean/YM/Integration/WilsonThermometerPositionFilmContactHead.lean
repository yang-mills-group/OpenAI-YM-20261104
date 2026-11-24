import YM.Comparison.RG02.Assembly.Contact

/-! The first surviving homogeneous field term reads a genuine smooth chart through its tangent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmContactHead
open Function Finset Comparison.RG02.Assembly
open scoped Classical BigOperators ContDiff Topology
variable {E X Y:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem single {k:ℕ} (c:OrderedFinpartition k) (h:c.length=k) (i:Fin c.length) :
    c.partSize i=1 := by
  have total:(∑j:Fin c.length,c.partSize j)=k:=by simpa using Fintype.card_congr c.equivSigma
  have pos:=c.partSize_pos i
  by_contra neq
  have less:(∑_j:Fin c.length,1)<∑j:Fin c.length,c.partSize j:=
    sum_lt_sum (fun j _=>c.partSize_pos j) ⟨i,mem_univ _,by omega⟩
  simp [total,h] at less

theorem tangent {k:ℕ} {f:X→Y} (H:GradeAt k f) {g:E→X} (smooth:ContDiffAt ℝ ω g 0)
    (home:g 0=0) (u:E) : jet (f ∘ g) k u=jet f k ((fderiv ℝ g 0) u) := by
  let L:=fderiv ℝ g 0
  have atG:ContDiffAt ℝ ω f (g 0):=home.symm ▸ H.smooth
  have atL:ContDiffAt ℝ ω f (L 0):=(L.map_zero).symm ▸ H.smooth
  have derived:iteratedFDeriv ℝ k (f ∘ g) 0=iteratedFDeriv ℝ k (f ∘ L) 0:=by
    rw [iteratedFDeriv_comp atG smooth le_top,iteratedFDeriv_comp atL L.contDiff.contDiffAt le_top,
      home,L.map_zero,FormalMultilinearSeries.taylorComp,FormalMultilinearSeries.taylorComp]
    apply sum_congr rfl
    intro c _
    ext v
    simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries]
    by_cases lower:c.length<k
    · rw [H.vanish _ lower];rfl
    · have len:c.length=k:=le_antisymm c.length_le (Nat.le_of_not_gt lower)
      congr 1
      funext i
      have equal:iteratedFDeriv ℝ (c.partSize i) g 0=iteratedFDeriv ℝ (c.partSize i) (⇑L) 0:=by
        rw [single c len i]
        ext w
        rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,L.fderiv]
      rw [equal]
  calc
    jet (f ∘ g) k u = jet (f ∘ L) k u := by unfold jet; rw [derived]
    _ = _ := jet_continuous_right L (H.smooth.of_le le_top) u

end YM.Integration.WilsonThermometerPositionFilmContactHead
