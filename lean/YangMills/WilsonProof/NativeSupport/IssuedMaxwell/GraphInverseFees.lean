import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphPrices
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.MonomialGauge
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphInverseFees
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Enh YM.FVA2.O.Bind YM.FVA2.Scale
open PowerSeries Filter Set YangMills.MSbar IssuedMaxwell.Reports
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup){n:ℕ}

theorem panel (q:Ordinary.Price (B g) n)(b:Q g.core):
    ∃S:Finset ((B g).toCoordinates.Key→₀ℕ),∃c:((B g).toCoordinates.Key→₀ℕ)→ℂ,
      ∀k t x,coeff k (GraphPrices.posted g q t x b)=∑m∈S,c m*MvPolynomial.coeff m (q b.h k t x).val:=by
  obtain ⟨S,c,record⟩:=MonomialGauge.original g b.h (paygrade b.item)
  refine ⟨S,c,fun k t x=>?_⟩
  rw [GraphPrices.posted,coeff_mk]
  exact record _

theorem original {A:Ordinary.Correlation (B g)}{a:Fin n→Ordinary.Label (B g)}
    {q:Ordinary.Price (B g) n}(purchased:Ordinary.ExteriorExpansion (B g) A a q):
    Markup (GraphPrices.posted g q):=by
  constructor
  · intro b k
    obtain ⟨S,c,refund⟩:=panel g q b
    have each (m):Pace (fun (x:Points n)(t:ℝ)=>MvPolynomial.coeff m (q b.h k t x).val):=by
      obtain ⟨D,file⟩:=purchased.polynomial b.h k m
      refine ⟨D,fun x=>?_⟩
      obtain ⟨P,degree,word⟩:=file x
      exact ⟨P,degree,funext word⟩
    change Pace (fun (x:Points n)(t:ℝ)=>coeff k (GraphPrices.posted g q t x b))
    simp_rw [refund]
    exact Pace.sum S (fun m _=>(Pace.narrow (fun (_:Points n)=>c m)).mul (each m))
  · intro t x hx
    funext b
    ext k
    change coeff k (mk _)=coeff k 0
    rw [coeff_mk,purchased.collision _ _ _ _ hx]
    exact (paygrade b.item).map_zero.trans (map_zero (coeff k)).symm
  · intro t b k
    obtain ⟨S,c,refund⟩:=panel g q b
    change ContinuousOn (fun (x:Points n)=>coeff k (GraphPrices.posted g q t x b)) (conf n)
    simp_rw [refund]
    exact continuousOn_finsetSum _ (fun m _=>continuousOn_const.mul (purchased.continuous b.h k t m))
  · intro K compact sep b l k _
    obtain ⟨S,c,refund⟩:=panel g q b
    have each (m):Rain 0 (fun (x:K)(t:ℝ)=>MvPolynomial.coeff m (q b.h k t x.val).val):=by
      obtain ⟨C,hC,L,price⟩:=purchased.bound K compact sep b.h k m
      refine ⟨C,hC,L,?_⟩
      filter_upwards [price] with t bound
      intro x
      simpa only [post,neg_zero,zero_mul,Real.exp_zero,mul_one] using bound x.val x.property
    change Rain 0 (fun (x:K)(t:ℝ)=>coeff k (GraphPrices.posted g q t x.val b))
    simp_rw [refund]
    exact Rain.sum S (fun m _=>(each m).scalar (c m))
end IssuedMaxwell.GraphInverseFees
end
