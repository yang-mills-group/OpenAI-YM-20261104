import YM.Integration.WilsonSeparatedOriginalSlabWatchTarget
import YM.Integration.WilsonMacroscopicRichWatchReader
import YM.Integration.WilsonMacroscopicRichWatchPlot

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchPhysical
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits PhysMS Lattice Wilson Next.UVStress
open WilsonMacroscopicRichWatchReader WilsonMacroscopicRichWatchPlot WilsonSeparatedOriginalSlabWatchSupport
open WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchBorn
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{I:Type}[Fintype I]

theorem current (F:Final C f S)(W:Watch C)(s:I→ℕ)(a:(i:I)→S.Field (s i))(x:Points (Fintype.card I))
    (live:joined W (native x)∈conf _):
    watch W s a x=whole S (native x) a (positions S (exterior S W)).ofLp
      (e:=fun i=>(OPE.tags S (exterior S W) i).1) (fun i=>(OPE.tags S (exterior S W) i).2):=by
  let E:=exterior S W;let e:=index S W;let y:=(positions S E).ofLp
  have places:y ∘ e=fixedSites W:=by funext i;exact congrArg Prod.fst (entry (S:=S) W i)
  have fields(i:Fin W.n):OPE.tags S E (e i)=S.classTokens (W.q i):=congrArg Prod.snd (entry (S:=S) W i)
  let l:=Equiv.sumCongr (Equiv.refl I) e
  have maps:beside (native x) y ∘l=beside (native x) (fixedSites W):=by
    funext i;cases i with
    | inl i=>rfl
    | inr i=>exact congrFun places i
  have hx:Injective (beside (native x) (fixedSites W)):=runs_conf.mp live
  have hy:Injective (beside (native x) y):=by
    intro i j ij;obtain ⟨i,rfl⟩:=l.surjective i;obtain ⟨j,rfl⟩:=l.surjective j
    apply congrArg l;apply hx;rw [←maps];exact ij
  refine Eq.trans ?_ (whole_perm S (Equiv.refl I) e F.room.kernel hy)
  change S.useAt S (joined W (native x)) (panel W s a ∘ runNames _)=
    S.useAt S (points (beside (native x) (y∘e) ∘runNames _)) (fun i=>Orbits.tags (stages a (fun j=>(OPE.tags S E (e j)).2)) (runNames _ i))
  rw [places];apply congrArg (S.useAt S _);funext i
  cases arm:runNames (I⊕Fin W.n) i with
  | inl j=>simp only [Function.comp_apply,arm];rfl
  | inr j=>simp only [Function.comp_apply,arm];exact (fields j).symm

end YM.Integration.WilsonSeparatedOriginalSlabWatchPhysical
