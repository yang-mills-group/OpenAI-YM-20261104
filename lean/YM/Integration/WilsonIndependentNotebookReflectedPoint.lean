import YM.Integration.WilsonIndependentNotebookReflectedComplex
import YM.Integration.WilsonOriginalPhysicalFruitVerse
import YM.Extra.SOURCE_HISTORIES.Motion

/-! The actual public label written on an original or surveyed point stencil transforms
with its own complex-conjugate test and unchanged valence compensation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 920000
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookReflectedPoint
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open Lattice RG Matrix Filter Function Finset Wilson PowerSeries Gauge
open Source Source.Drops Labels
open WilsonCoeffUV.Embroider Extra.Histories
open WilsonOriginalPhysicalFruitVerse (written)
open scoped BigOperators Classical
variable {G:Gauge}{d:ℕ}

private theorem page (F:Frame G d)(v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(b:Alma F)(t:ℕ):
    coeff t (written F v p b)=
      if rankS (notar F b)=0 ∧ valence F b=t then p (v (sheet F b)) else 0:=by
  by_cases h:rankS (notar F b)=0
  · simp only [written,show rankS b.val.2=0 from h,if_true,coeff_monomial,h,true_and,@eq_comm _ t (valence F b)]
  · simp only [written,show ¬rankS b.val.2=0 from h,if_false,map_zero,h,false_and]

theorem signed (F:Frame G d)(s:Signed)(v:F.Coeff)(p:ℂ →L[ℝ] ℝ):
    written F (F.act s.ortho v) p=Cosmos.paintC F s*ᵥwritten F v p:=by
  funext b
  ext1 t
  obtain ⟨u,valid,tag⟩:=drift F s b
  have w:notar F b=spindle s u:=congrArg Prod.snd tag
  have deg:rankS (notar F b)=rankS u:=w ▸ spun_card s u
  let paid:F.Index→ℝ:=fun i=>if rankS u=0 ∧ valence F b=t then p (v i) else 0
  have owns (j:Alma F)(pj:notar F j=u)(ht:F.grades (sheet F j)=F.grades (sheet F b)):
      coeff t (written F v p j)=paid (sheet F j):=by
    have vv:valence F j=valence F b:=congrArg Prod.snd ht
    rw [page,pj,vv]
  have recast:=reducing F s (sheet F b) u _ valid rfl b tag (fun i=>coeff t (written F v p i)) paid owns
  have raw (j:F.Index):p ((F.act s.ortho v) j)=∑i,bleached F s.ortho j i*p (v i):=by
    rw [pollenC,map_sum]
    apply sum_congr rfl
    intro i _
    rw [←Complex.real_smul,map_smul]
    rfl
  calc
    coeff t (written F (F.act s.ortho v) p b)=
      (if rankS u=0 ∧ valence F b=t then p ((F.act s.ortho v) (sheet F b)) else 0):=by rw [page,deg]
    _=hue s u.val*(∑i,bleached F s.ortho (sheet F b) i*paid i):=by
      by_cases retained:rankS u=0 ∧ valence F b=t
      · have zero:u.val=0:=Multiset.card_eq_zero.mp retained.1
        simp only [paid,retained,zero,hue,Multiset.map_zero,Multiset.prod_zero,one_mul]
        exact raw _
      · simp [paid,retained]
    _=(∑i,blueIn F s b i*coeff t (written F v p i)):=recast.symm
    _=coeff t ((Cosmos.paintC F s*ᵥwritten F v p) b):=by
      simp only [Matrix.mulVec,dotProduct,map_sum,Cosmos.paintC,Matrix.of_apply,coeff_C_mul]

def lens (bar:Bool)(p:ℂ →L[ℝ] ℝ):ℂ →L[ℝ] ℝ:=
  if bar then p.comp Complex.conjCLE.toContinuousLinearMap else p

theorem original (F:Frame G d)(s:Motion)(v:F.Coeff)(p:ℂ →L[ℝ] ℝ):
    written F (Motion.patch F s v) p=Cosmos.paintC F s.1*ᵥwritten F v (lens s.2 p):=by
  rw [←signed]
  rcases s with ⟨s,_|_⟩
  · rfl
  · funext j
    simp only [Motion.patch,lens,if_true,written,Pi.star_apply,ContinuousLinearMap.comp_apply]
    rfl

end YM.Integration.WilsonIndependentNotebookReflectedPoint
