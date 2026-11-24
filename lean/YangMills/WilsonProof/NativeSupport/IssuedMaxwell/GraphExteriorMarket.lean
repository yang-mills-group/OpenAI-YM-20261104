import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphSpectralTail
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphBasisExterior
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphOutside
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphExteriorMarket
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Bind YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.FVA2.Scale.Equator PowerSeries Filter Set
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup){n m:ℕ}

theorem signed (u:Scan g.core n)(b:Fin m→Ordinary.Label (B g))(p:FLog g.core n)
    (h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    read g (n+m) k (Fin.append (labels g u) b) (forest (squeeze t x) y)-
      Ordinary.truncation (B g) (read g) (GraphPrices.entered g p) (totalG u) h k b t x y=
    ∑s:GraphTail.entry g b,GraphTail.income g b s*
      coeff k (Submit (GraphTruncation.album g) u (GraphTail.marks g b s) t p h x y):=by
  rw [GraphTail.expanded,GraphSpectralTail.truncated,←Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _=>?_
  rw [GraphTruncation.submitted,mul_sub]

theorem original (simple:g.IsSimple)(u:Scan g.core n):
    Ordinary.ExteriorExpansion (B g) (read g) (labels g u) (GraphBasisExterior.price g u):=by
  have paid:OPEA (GraphTruncation.album g) u (GraphBasisExterior.ticket g u):=(ExteriorReceipt.original g simple u).1
  let p:=GraphBasisExterior.ticket g u
  refine ⟨GraphPrices.degree g p,GraphPriceCoordinates.collision g p paid.toMarkup,
    GraphPriceCoordinates.polynomial g p paid.toMarkup,GraphPriceCoordinates.continuous g p paid.toMarkup,
    fun K ck sep=>GraphPriceCompact.original g p paid.toMarkup K ck sep,?_⟩
  intro K ck sep m b E ce ext h k
  have outside:E⊆Outside m:=fun y hy=>(GraphOutside.original y).mpr (ext y hy)
  let rate:ℝ:=(h:ℝ)+1-(totalG u:ℝ)
  let held (s:GraphTail.entry g b)(i:K×E)(t:ℝ):ℂ:=
    coeff k (Submit (GraphTruncation.album g) u (GraphTail.marks g b s) t p h i.1.val i.2.val)
  have earned (s):Rain rate (held s):=(paid.through K ck sep h (k+1) m E (GraphTail.marks g b s) ce outside)
    k (Nat.lt_succ_self k)
  obtain ⟨C,pos,L,income⟩:=Rain.sum Finset.univ (fun s _=>(earned s).scalar (GraphTail.income g b s))
  refine ⟨C,pos,L,?_⟩
  filter_upwards [income] with t certificate
  intro x hx y hy
  have report:=certificate (⟨x,hx⟩,⟨y,hy⟩)
  have settled:=signed g u b p h k t x y
  have balance:‖∑s,GraphTail.income g b s*held s (⟨x,hx⟩,⟨y,hy⟩) t‖≤
      C*(1+t)^L*Real.exp (((totalG u:ℝ)-(h:ℝ)-1)*t):=by
    simpa only [rate,post,neg_sub,sub_sub,neg_add_rev,neg_neg,mul_assoc] using report
  exact (congrArg (fun z:ℂ=>‖z‖) settled).le.trans balance
end IssuedMaxwell.GraphExteriorMarket
end
