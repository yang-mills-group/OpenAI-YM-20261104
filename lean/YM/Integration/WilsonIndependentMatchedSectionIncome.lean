import YM.Integration.WilsonIndependentMatchedCoverProfile
import YM.Integration.WilsonIndependentMatchedNamedPair

/-! Cutoff-uniform input wages for the actual section cylinders on the cover.
The stencil's finite set of addressed links bounds every order needed by a
fixed Taylor request. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedSectionIncome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open scoped BigOperators Topology Classical
variable {G:Gauge}{d D k e u:ℕ}{F:Labels.Frame G d}

def leaf (T:SectionData F)(w:d<D)(a:Alma F) : TowerS G D:=
  vein ((fun n i => herald T w i n),anthem T w) a

theorem rooted (T:SectionData F)(w:d<D)(a:Alma F)(u j r:ℕ):
    ∃ A:ℝ,Fruit 0 1 u ((leaf T w a).2 j r) A := by
  classical
  let box:=Finset.univ.image (fun f:Fin r→Toe T => dance T ∘ f)
  let g:=fun x=>hedge (0:Cover) 1 u x*‖((leaf T w a).2 j r) x‖
  have nn:∀x,0≤g x:=fun x=>mul_nonneg (hedge_nn zero_le_one _) (norm_nonneg _)
  have outside (x)(hx:x∉box):g x=0:=by
    have missing:x∉Set.range (fun f:Fin r→Toe T=> dance T ∘ f):=by
      rintro ⟨f,rfl⟩
      exact hx (Finset.mem_image.mpr ⟨f,Finset.mem_univ _,rfl⟩)
    have zero:(anthem T w a j r) x=0:=by
      unfold anthem
      by_cases rank:valence F a+j=r
      · subst r
        rw [shine_lit]
        simp [carte,treasury T (sheet F a) x missing]
      · rw [shine_dark rank]; rfl
    change _ * ‖(anthem T w a j r) x‖=0
    rw [zero,norm_zero,mul_zero]
  exact ⟨∑ x∈box,g x,nn,summable_of_ne_finset_zero outside,(tsum_eq_sum outside).le⟩

theorem salary (T:SectionData F)(w:d<D)(a:Alma F)(e u:ℕ):
    ∃ A:ℝ,0≤A ∧ ∀j r:ℕ,j≤e→Fruit 0 1 u ((leaf T w a).2 j r) A := by
  classical
  choose cost spent using fun i:Fin (e+1)=>rooted T w a u i.val (valence F a+i.val)
  have nn i:= (spent i).C
  refine ⟨∑i,cost i,Finset.sum_nonneg (fun i _=>nn i),?_⟩
  intro j r hj
  let i:Fin (e+1):=⟨j,by omega⟩
  by_cases live:valence F a+j=r
  · subst r
    exact (spent i).more (Finset.single_le_sum (fun b _=>nn b) (Finset.mem_univ i))
  · have quiet:((leaf T w a).2 j r)=0:=shine_dark live
    rw [quiet]
    exact Fruit.zero.more (Finset.sum_nonneg (fun n _=>nn n))

theorem actual (T:SectionData F)(w:d<D)(a:Alma F)(H:Hol G)
    (law:T.Sound H)(pop:Bid.pop T)(fits:valence F a≤k)(e u:ℕ):
    On k (leaf T w a) ∧ ∃ A:ℝ,0≤A ∧ ∀j r:ℕ,j≤e→Fruit 0 1 u ((leaf T w a).2 j r) A :=
  ⟨hailed _ (freshly T H w law pop) a fits,salary T w a e u⟩

/-- Both actual section catalogues receive the same kind of rooted wage on
their own geometry. No smooth representative is substituted for a group field. -/
theorem named (R:Run G)(W:Initialize G)(physicalSurvey:Bool)(d:ℕ)(w:d<D)
    (a:Alma (R.family.labels.level d))(cap:valence _ a≤k)(e u:ℕ):
    let T:=WilsonIndependentMatchedNamedPair.sectionAt R W physicalSurvey d
    On k (leaf T w a) ∧ ∃ A:ℝ,0≤A ∧ ∀j r:ℕ,j≤e→Fruit 0 1 u ((leaf T w a).2 j r) A := by
  cases physicalSurvey with
  | true =>
    have h:=WilsonOriginalPivotWardSurvey.issued R W d
    exact actual _ w a W.hol h.1 h.2.1 cap e u
  | false => exact actual _ w a _ (R.makes.sections d) (FVAAlt2.Block.clothes R d) cap e u

end YM.Integration.WilsonIndependentMatchedSectionIncome
