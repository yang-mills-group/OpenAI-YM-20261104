import YM.Integration.WilsonIndependentMatchedOpeningFiled
import YM.Integration.WilsonOlderFreshSoftSocketFullContrast

/-! A planted difference of complete fitted sections retains every test derivative and scalar.
The rooted zero-moment charge at any actual cover point uses the signed power-series coefficients. -/
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketVerseSeed
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedOpeningFiled (planted)
open scoped Classical BigOperators
variable {G:Gauge}{D d:ℕ}(R:Run G)(W:Initialize G)
local notation "F" => R.family.labels.level d

theorem linear (s:Bool)(w:d<D)(b:Volume D)(x y:Verse F)(o:Cover):
    planted R W s w b (x-y) o=planted R W s w b x o-planted R W s w b y o:=by
  have split:Shrine (plate (sectionAt R W s d) w) (x-y)=
      Shrine (plate (sectionAt R W s d) w) x-Shrine (plate (sectionAt R W s d) w) y:=by
    apply Prod.ext
    · funext n j r a
      simp only [Shrine,Stem,Prod.fst_sub,Prod.fst_sum,Finset.sum_apply,Pi.sub_apply,affix,map_sub,sub_smul,Finset.sum_sub_distrib,Pi.smul_apply]
    · funext j r a
      simp only [Shrine,Stem,Prod.snd_sub,Prod.snd_sum,Finset.sum_apply,Pi.sub_apply,affix,map_sub,sub_smul,Finset.sum_sub_distrib,Pi.smul_apply]
  unfold planted
  rw [split]
  apply Prod.ext
  · funext n j r a
    change (ContinuousLinearMap.apply ℝ ℝ b) (_-_) = _-_
    exact map_sub _ _ _
  · funext j r a
    change (ContinuousLinearMap.apply ℝ ℝ b) (_-_) = _-_
    exact map_sub _ _ _

theorem moved{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V] {j r:ℕ}
    (P:Era G V)(f:V→L[ℝ] ℝ)(o:Cover){B:ℝ}(input:Fruit 0 1 0 (P.2 j r) B):
    Fruit 0 0 0 ((shifted (tuftV f P) o).2 j r) (‖f‖*B):=by
  let e:Equiv.Perm (Fin r→YForest G):=Equiv.piCongrRight fun _=>jog (-o)
  let g:=fun a=>‖P.2 j r a‖
  have raw:SumBudget g B:=by simpa [Fruit,Award,hedge,autumn,g] using input
  have moved:SumBudget (g∘e) B:=⟨fun a=>raw.1 _,e.summable_iff.mpr raw.2.1,(e.tsum_eq g).le.trans raw.2.2⟩
  let h:=fun a=>‖f (P.2 j r (e a))‖
  have cap (a):h a≤‖f‖*(g∘e) a:=f.le_opNorm _
  have positive (a):0≤h a:=norm_nonneg _
  have sum:=moved.2.1.mul_left ‖f‖
  have hs:Summable h:=Summable.of_nonneg_of_le positive cap sum
  have bound:(∑'a,h a)≤‖f‖*B:=by
    calc (∑'a,h a)≤∑'a,‖f‖*(g∘e) a:=hs.tsum_le_tsum cap sum
         _=‖f‖*(∑'a,(g∘e) a):=tsum_mul_left
         _≤‖f‖*B:=mul_le_mul_of_nonneg_left moved.2.2 (norm_nonneg _)
  have funded:SumBudget h (‖f‖*B):=⟨positive,hs,bound⟩
  change SumBudget (fun a=>hedge 0 0 0 a * ‖f (P.2 j r (e a))‖) _
  simpa only [hedge,autumn,pow_zero,one_mul] using funded

theorem original (s:Bool)(w:d<D)(e:ℕ):
    ∃A:Alma F→ℝ,(∀a,0≤A a)∧∀(x y:Verse F)(b:Volume D)(o:Cover),
      let P:=planted R W s w b x o-planted R W s w b y o
      Auth d P ∧ 0≤charge e (x-y) A ∧
      Saturation e 0 0 P.2 0 (‖ContinuousLinearMap.apply ℝ ℝ b‖*charge e (x-y) A):=by
  obtain ⟨A,positive,hired⟩:=WilsonIndependentMatchedFiledIncome.named R W s d w le_rfl e 0
  refine ⟨A,positive,?_⟩
  intro x y b o P
  dsimp only [P]
  rw [←linear]
  exact ⟨WilsonIndependentMatchedOpeningFiled.enrolled R W s w b (x-y) o,(hired (x-y)).2.1,
    fun j hj r _=>moved _ _ _ ((hired (x-y)).2.2 j r hj)⟩

end YM.Integration.WilsonOlderFreshSoftSocketVerseSeed
