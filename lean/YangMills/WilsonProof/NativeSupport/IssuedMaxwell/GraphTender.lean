import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphExteriorMarket
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphTender
open YM YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Enh
open YM.FVA2.Scale PowerSeries Set Filter
open IssuedMaxwell.Reports
open scoped BigOperators Classical
variable {G:Gauge}{n:ℕ}{I:Type}[Fintype I]

def combine (c:I→ℂ)(p:I→FLog G n):FLog G n:=fun t x b=>∑i,C (c i)*p i t x b
theorem measure (c:I→ℂ)(p:I→FLog G n)(t x b k):
    coeff k (combine c p t x b)=∑i,c i*coeff k (p i t x b):=by
  rw [combine,map_sum]
  simp only [coeff_C_mul]

theorem boughtClocks (c:I→ℂ)(p:I→FLog G n)(financed:∀i,Markup (p i))(K:Set (Points n))
    (ck:IsCompact K)(sep:K⊆conf n)(b:Q G)(d k:ℕ)(hk:k<d):
    Rain 0 (fun (x:K)(t:ℝ)=>coeff k (combine c p t x.val b)):=by
  let row (i:I)(x:K)(t:ℝ):ℂ:=coeff k (p i t x.val b)
  have each (i:I):Rain 0 (row i):=(financed i).clocks K ck sep b d k hk
  have cell (i:I):Rain 0 (fun (x:K)(t:ℝ)=>c i*row i x t):=(each i).scalar (c i)
  have sum:Rain 0 (fun (x:K)(t:ℝ)=>∑i:I,c i*row i x t):=
    Rain.sum (a:=0) (Finset.univ (α:=I)) (f:=fun (i:I)(x:K)(t:ℝ)=>c i*row i x t) (fun (i:I) _=>cell i)
  simpa only [measure,row] using sum

theorem purchased (c:I→ℂ)(p:I→FLog G n)(financed:∀i,Markup (p i)):Markup (combine c p):=by
  constructor
  · intro b k
    change Pace (fun (x:Points n)(t:ℝ)=>coeff k (combine c p t x b))
    simp_rw [measure]
    exact Pace.sum Finset.univ (fun i _=>(Pace.narrow (fun (_:Points n)=>c i)).mul ((financed i).poly b k))
  · intro t x hx
    funext b
    change (∑i,C (c i)*p i t x b)=0
    simp only [(financed _).off t x hx,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  · intro t b k
    change ContinuousOn (fun (x:Points n)=>coeff k (combine c p t x b)) (conf n)
    simp_rw [measure]
    exact continuousOn_finsetSum _ (fun i _=>continuousOn_const.mul ((financed i).stays t b k))
  · intro K ck sep b d k hk
    exact boughtClocks c p financed K ck sep b d k hk

theorem posting (g:YangMills.GaugeGroup)(c:I→ℂ)(p:I→FLog g.core n)(w k:ℕ)(t:ℝ)(x:Points n):
    GraphPrices.entered g (combine c p) w k t x=∑i,c i • GraphPrices.entered g (p i) w k t x:=by
  change (∑b:Grade g.core w,coeff k (combine c p t x (own b)) • vertex b)=_
  simp_rw [measure,Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _=>?_
  change (∑b:Grade g.core w,(c i*coeff k (p i t x (own b))) • vertex b)=c i •
    (∑b:Grade g.core w,coeff k (p i t x (own b)) • vertex b)
  rw [Finset.smul_sum]
  simp only [mul_smul]
end IssuedMaxwell.GraphTender
end
