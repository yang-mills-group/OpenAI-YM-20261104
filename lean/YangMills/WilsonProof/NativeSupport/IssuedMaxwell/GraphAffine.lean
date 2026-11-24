import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphPriceFusion
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphAffine
open YM YM.FVA2 YM.FVA2.O YM.FVA2.O.Project PowerSeries YangMills.MSbar
open IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical Matrix
variable {G:Gauge}{n m:ℕ}

def vote:Fin 3→ℂ:=![1,1,-1]
def receipts (p q r:FLog G n):Fin 3→FLog G n:=![p,q,r]
def adjusted (p q r:FLog G n):FLog G n:=GraphTender.combine vote (receipts p q r)
theorem full (p q r:FLog G n)(t x b):adjusted p q r t x b=p t x b+q t x b-r t x b:=by
  simp [adjusted,GraphTender.combine,vote,receipts,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc]
theorem cleared (p q r:FLog G n)(a:Markup p)(b:Markup q)(c:Markup r):Markup (adjusted p q r):=by
  refine GraphTender.purchased _ _ ?_
  intro i
  fin_cases i
  · exact a
  · exact b
  · exact c

theorem original (g:YangMills.GaugeGroup)(p q r:FLog g.core n)(b:Fin m→Ordinary.Label (B g))
    (e h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    let T:=fun z=>Ordinary.truncation (B g) (read g) (GraphPrices.entered g z) e h k b t x y
    T (adjusted p q r)=T p+T q-T r:=by
  dsimp only
  rw [adjusted,GraphPriceFusion.original]
  simp [vote,receipts,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc]
end IssuedMaxwell.GraphAffine
end
