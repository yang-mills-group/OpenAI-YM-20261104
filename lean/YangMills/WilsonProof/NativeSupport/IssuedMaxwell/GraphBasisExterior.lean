import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphTruncation
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphPriceCompact
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphBasisExterior
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Bind YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.FVA2.Scale.Equator PowerSeries Filter Set
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup)(simple:g.IsSimple){n:ℕ}

def ticket (u:Scan g.core n):FLog g.core n:=
  LogPricing (wave (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core)) u
def price (u:Scan g.core n):Ordinary.Price (B g) n:=GraphPrices.entered g (ticket g u)

include simple in
theorem original (u:Scan g.core n)(K:Set (Points n))(ck:IsCompact K)(sep:K⊆conf n)
    (h k m:ℕ)(E:Set (Points m))(v:Scan g.core m)(ce:IsCompact E)(outside:E⊆Outside m):
    ∃c:ℝ,0<c ∧ ∃L:ℕ,∀ᶠ t:ℝ in atTop,∀x∈K,∀y∈E,
      ‖read g (n+m) k (Fin.append (labels g u) (labels g v)) (forest (Real.exp (-t) • x) y)-
        Ordinary.truncation (B g) (read g) (price g u) (totalG u) h k (labels g v) t x y‖≤
        c*(1+t)^L*Real.exp (((totalG u:ℝ)-(h:ℝ)-1)*t):=by
  obtain ⟨c,hc,L,financed⟩:=(ExteriorReceipt.original g simple u).2.2 K ck sep h k m E v ce outside
  refine ⟨c,hc,L,?_⟩
  filter_upwards [financed] with t wage
  intro x hx y hy
  have equality:=GraphTruncation.submitted g u v (ticket g u) h k t x y
  exact (congrArg (fun z:ℂ=>‖z‖) equality).symm.le.trans (wage x hx y hy)
end IssuedMaxwell.GraphBasisExterior
end
