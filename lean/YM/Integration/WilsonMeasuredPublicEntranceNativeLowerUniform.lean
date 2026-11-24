import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRefined
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSame
import YM.Integration.WilsonPhysicalPositionHalfRange
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerUniform
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS PhysMS.Frame
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPhysicalStationGradedLowerPanel (left right frame)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free)
open WilsonMeasuredPublicEntranceNativeLowerLeft (ears coefficients representative)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel row pivot vote)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
local notation "D" => Table.Field (Bel R.family.book)

open WilsonMeasuredPublicEntranceNativeLowerRefined (Refined)
open WilsonPhysicalPositionReflectedReturn (reading)
open WilsonPhysicalPositionUniformBranches (change)

def Offered (U:ℝ→tower S)(d:ℕ):Prop:=
  ∀(r t:ℕ→ℝ)(s:ℝ),0<s→Tendsto r atTop trail→Tendsto t atTop (𝓝 s)→
    (∀n,0<r n)→(∀n,t n∈Icc (1/2:ℝ) 1)→(∀ᶠ n in atTop,t n<1)→
    ∀k,0<k→k≤d→let T:=R.family.labels.level k
      ∀u v:T.Index,(T.grades u).1=k→(T.grades v).1=k→(T.grades u).2≤(T.grades v).2→Refined R F atTop U r t s k u v

set_option maxHeartbeats 2400000 in
theorem tested {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){d:ℕ}(file:Offered R F U d)
    (v:D d){eps:ℝ}(ep:0<eps):∀ᶠ r in trail,∀t∈Icc (1/2:ℝ) 1,reading F J v r t≤eps:=by
  let X:=D d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  letI : ProperSpace (X→L[ℂ]X):=FiniteDimensional.proper ℂ _
  obtain ⟨B,paid,bound⟩:=PhysMS.Frame.comparison F d J lead
  have half:0<(1/2:ℝ):=by norm_num
  by_contra missed
  have low:∀ᶠ r in trail,0<r:=self_mem_nhdsWithin
  obtain ⟨r,near,denied⟩:=Filter.exists_seq_forall_of_frequently ((Filter.not_eventually.mp missed).and_eventually low)
  have witnesses n:∃t:ℝ,t∈Icc (1/2:ℝ) 1 ∧ eps<reading F J v (r n) t:=by
    obtain ⟨t,den⟩:=not_forall.mp (denied n).1
    obtain ⟨ht,miss⟩:=not_forall.mp den
    exact ⟨t,ht,lt_of_not_ge miss⟩
  choose t interval failure using witnesses
  let C (n:ℕ):X→L[ℂ]X:=change J d (r n) (t n) (half.trans_le (interval n).1)
  have kept:∀ᶠ n in atTop,(t n,C n)∈Icc (1/2:ℝ) 1 ×ˢ Metric.closedBall 0 B:=by
    filter_upwards [near.eventually (bound _ half)] with n dose
    refine ⟨interval n,?_⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans paid) (dose (t n) (interval n)).1
  obtain ⟨⟨s,Z⟩,live,pick,increases,conv⟩:=(isCompact_Icc.prod
    (isCompact_closedBall (0:X→L[ℂ]X) B)).tendsto_subseq' kept.frequently
  change Tendsto (fun n=>(t (pick n),C (pick n))) atTop (𝓝 (s,Z)) at conv
  have ratio:Tendsto (fun n=>t (pick n)) atTop (𝓝 s):= (continuous_fst.tendsto (s,Z)).comp conv
  have operators:=(continuous_snd.tendsto (s,Z)).comp conv
  have near':Tendsto (fun n=>r (pick n)) atTop trail:=near.comp increases.tendsto_atTop
  let pos n:0<t (pick n):=half.trans_le (interval (pick n)).1
  have arrow (w:X):Tendsto (fun n=>PhysMS.Frame.cocycle d J (r (pick n)) (t (pick n)) (pos n) w) atTop (𝓝 (Z w)):=
    ((ContinuousLinearMap.apply ℂ X w).continuous.tendsto Z).comp operators
  have sp:=half.trans_le live.1.1
  have fixed:Z.toLinearMap=1:=by
    by_cases equal:∃ᶠ n in atTop,t (pick n)=1
    · obtain ⟨sub,grows,allEq⟩:=Filter.exists_seq_forall_of_frequently equal
      apply LinearMap.ext
      intro w
      apply tendsto_nhds_unique ((arrow w).comp grows)
      exact tendsto_const_nhds.congr' (Eventually.of_forall fun n=>(WilsonMeasuredPublicEntranceNativeLowerSame.original R J w
        (r (pick (sub n))) (t (pick (sub n))) (pos (sub n)) (allEq n)).symm)
    have apart:∀ᶠn in atTop,t (pick n)<1:=(not_frequently.mp equal).mono fun n ne=>lt_of_le_of_ne (interval (pick n)).2 ne
    exact WilsonMeasuredPublicEntranceNativeLowerRefined.original R F lead aligned near' ratio sp pos Z.toLinearMap arrow
      (file (r∘pick) (t∘pick) s sp near' ratio (fun n=>(denied (pick n)).2) (fun n=>interval (pick n)) apart)
  have seen:=WilsonPhysicalPositionReflectedReturn.original F J lead near' sp ratio pos Z.toLinearMap arrow v
  have zero:Tendsto (fun n=>reading F J v (r (pick n)) (t (pick n))) atTop (𝓝 0):=by
    simpa only [Function.comp_def,fixed,Module.End.one_apply,sub_self,map_zero,LinearMap.zero_apply] using seen
  exact (not_le_of_gt ep) (ge_of_tendsto zero (Eventually.of_forall fun n=>(failure (pick n)).le))

theorem original {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J)(store:Store G){d:ℕ}
    (file:Offered R F U d):∀c:ℝ,0<c→WilsonPhysicalPositionHalfRange.uniform J d c:=by
  obtain ⟨v,_,g,hg,earn⟩:=WilsonPhysicalPositionHalfRange.original F J lead store d
  exact earn (tested R F lead aligned file v hg)

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerUniform
end
