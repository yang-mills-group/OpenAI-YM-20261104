import YM.Integration.WilsonIndependentMatchedSectionIncome

/-! The entire finite Shrine column is admitted using the Taylor coefficients
actually submitted in its verse. All entrance costs are paid before cutoff and
period, separately from the compensated cover comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFiledIncome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonIndependentMatchedSectionIncome
open scoped BigOperators Topology Classical
variable {G:Gauge}{d D k e u:ℕ}{F:Labels.Frame G d}

def plate (T:SectionData F)(w:d<D):Island F D:=((fun n i=>herald T w i n),anthem T w)
def allot (e:ℕ)(c:Blue.Cost)(A:ℝ):ℝ:=
  ∑ j∈Finset.range (e+1),∑t∈Finset.HasAntidiagonal.antidiagonal j,|coeff t.1 c| * A
def charge (q:ℕ)(c:Verse F)(A:Alma F→ℝ):ℝ:=∑i,allot q (c i) (A i)

lemma nonneg {A:ℝ}(ha:0≤A)(c:Blue.Cost)(j:ℕ):0≤allot j c A:=
 Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>mul_nonneg (abs_nonneg _) ha

theorem stem {P:TowerS G D}{A:ℝ}(ha:0≤A)(c:Blue.Cost)
    (funded:∀j r:ℕ,j≤e→Fruit 0 1 u (P.2 j r) A):
    ∀j r,j≤e→ Fruit 0 1 u ((Stem c P).2 j r) (allot e c A) := by
  intro j r hj
  have one (t:ℕ×ℕ)(ht:t∈Finset.HasAntidiagonal.antidiagonal j):
      Fruit 0 1 u (coeff t.1 c • P.2 t.2 r) (|coeff t.1 c| * A):=
    (funded t.2 r (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp ht; omega)).μ _
  have many:=Fruit.sum one zero_le_one
  have cap:(∑t∈Finset.HasAntidiagonal.antidiagonal j,|coeff t.1 c| *A)≤allot e c A:=
    Finset.single_le_sum (f:=fun j=>∑t∈Finset.HasAntidiagonal.antidiagonal j,|coeff t.1 c| *A)
      (fun i _=>Finset.sum_nonneg fun _ _=>mul_nonneg (abs_nonneg _) ha)
      (Finset.mem_range.mpr (by omega))
  simpa only [Stem,affix,Finset.sum_apply,Pi.smul_apply] using many.more cap

theorem original (T:SectionData F)(w:d<D)(H:Hol G)(law:T.Sound H)(s:Bid.pop T)
    (capacity:d≤k)(e u:ℕ):
    ∃ A:Alma F→ℝ,(∀i,0≤A i) ∧ ∀c:Verse F,
      On k (Shrine (plate T w) c) ∧ 0≤charge e c A ∧ ∀j r,j≤e→
        Fruit 0 1 u ((Shrine (plate T w) c).2 j r) (charge e c A) := by
  classical
  choose A nn spent using fun i=>salary T w i e u
  refine ⟨A,nn,fun c=>⟨Shrine_on _ (freshly T H w law s) c capacity,?_,?_⟩⟩
  · exact Finset.sum_nonneg fun i _=>nonneg (nn i) _ _
  · intro j r hj
    have one (i:Alma F)(_hi:i∈(Finset.univ:Finset (Alma F))):
        Fruit 0 1 u ((Stem (c i) (leaf T w i)).2 j r) (allot e (c i) (A i)) :=
      stem (nn i) (c i) (spent i) j r hj
    simpa only [Shrine,plate,WilsonIndependentMatchedSectionIncome.leaf,Prod.snd_sum,Finset.sum_apply,charge]
      using Fruit.sum one zero_le_one

theorem named (R:Run G)(W:Initialize G)(s:Bool)(d:ℕ)(w:d<D)(capacity:d≤k)(e u:ℕ):
    let T:=WilsonIndependentMatchedNamedPair.sectionAt R W s d
    ∃ A:Alma (R.family.labels.level d)→ℝ,(∀i,0≤A i) ∧ ∀c:Verse (R.family.labels.level d),
      On k (Shrine (plate T w) c) ∧ 0≤charge e c A ∧ ∀j r,j≤e→
        Fruit 0 1 u ((Shrine (plate T w) c).2 j r) (charge e c A) := by
  cases s with
  | true =>
    have h:=WilsonOriginalPivotWardSurvey.issued R W d
    exact original _ w W.hol h.1 h.2.1 capacity e u
  | false => exact original _ w _ (R.makes.sections d) (FVAAlt2.Block.clothes R d) capacity e u

end YM.Integration.WilsonIndependentMatchedFiledIncome
