import YM.Integration.WilsonIndependentMatchedFiledIncome

/-! The real and imaginary readings of the unshifted finite physical section.
The valence on each term is restored inside the submitted verse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFruitVerse
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonIndependentMatchedSectionIncome
open scoped BigOperators Topology Classical
open Finset WilsonIndependentMatchedFiledIncome
variable {G:Gauge}{d:ℕ}(F:Labels.Frame G d)

def written (v:F.Coeff)(p:ℂ →L[ℝ] ℝ):Verse F:=fun i=>
  if rankS i.val.2=0 then monomial (valence F i) (p (v (sheet F i))) else 0

theorem coefficient (v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(i:Alma F)(t:ℕ):
    |coeff t (written F v p i)| ≤ ‖p‖*F.coeffSize v:=by
  have nn:0 ≤ F.coeffSize v:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have price:(‖p‖*‖v (sheet F i)‖) ≤ ‖p‖*F.coeffSize v:=mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (s:=univ) (f:=fun b:F.Index=>‖v b‖) (fun _ _=>norm_nonneg _) (mem_univ _)) (norm_nonneg _)
  unfold written
  split
  · rw [coeff_monomial]
    split
    · exact (p.le_opNorm _).trans price
    · simpa only [abs_zero] using mul_nonneg (norm_nonneg p) nn
  · simp only [map_zero,abs_zero]; exact mul_nonneg (norm_nonneg _) nn

theorem bought (v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(e:ℕ)(A:Alma F → ℝ)(pos:∀i,0 ≤ A i):
    WilsonIndependentMatchedFiledIncome.charge e (written F v p) A ≤ (∑i:Alma F,∑j∈range (e+1),∑_∈Finset.HasAntidiagonal.antidiagonal j,A i)*
      (‖p‖*F.coeffSize v):=by
  unfold WilsonIndependentMatchedFiledIncome.charge allot
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>Finset.sum_le_sum fun ij _=>?_
  simpa only [mul_comm (A i)] using mul_le_mul_of_nonneg_right (coefficient F v p i ij.1) (pos i)

theorem named (R:Run G)(W:Initialize G)(survey:Bool)(d D k e u:ℕ)(hd:d<D)(fits:d ≤ k):
    let S:=R.family.labels.level d
    let T:=WilsonIndependentMatchedNamedPair.sectionAt R W survey d
    ∃C₀:ℝ,0 ≤ C₀ ∧ ∀(v:S.Coeff)(p:ℂ →L[ℝ] ℝ),
      let P:=Shrine (plate T hd) (written S v p)
      On k P ∧ ∀j r:ℕ,j ≤ e → Fruit 0 1 u (P.2 j r) (C₀*(‖p‖*S.coeffSize v)):=by
  intro S T
  obtain ⟨A,nn,serve⟩:=WilsonIndependentMatchedFiledIncome.named R W survey d hd fits e u
  refine ⟨∑i:Alma S,∑j∈range (e+1),∑_∈Finset.HasAntidiagonal.antidiagonal j,A i,
    Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>nn i))),?_⟩
  intro v p P
  obtain ⟨licensed,_,priced⟩:=serve (written S v p)
  exact ⟨licensed,fun j r h=>(priced j r h).more (bought S v p e A nn)⟩

end YM.Integration.WilsonOriginalPhysicalFruitVerse
end
