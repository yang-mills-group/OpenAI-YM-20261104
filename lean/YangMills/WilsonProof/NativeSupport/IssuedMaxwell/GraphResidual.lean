import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphRevenue
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphAffine
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphResidual
open YM YM.FVA2 YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Project
open Set Filter YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation IssuedMaxwell.GraphRevenue
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup){n m:ℕ}

def service (p:FLog g.core n)(q r:Ordinary.Price (B g) n):FLog g.core n:=
  GraphAffine.adjusted p (GraphPrices.posted g q) (GraphPrices.posted g r)

theorem account (a a₀:Fin n→Ordinary.Label (B g))(p:FLog g.core n)(q r:Ordinary.Price (B g) n)
    (cq:Ordinary.ExteriorExpansion (B g) (read g) a q)(cr:Ordinary.ExteriorExpansion (B g) (read g) a r)
    (b:Fin m→Ordinary.Label (B g))(h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    due g a₀ (GraphPrices.entered g (service g p q r)) b h k t x y=
      due g a₀ (GraphPrices.entered g p) b h k t x y+
      (Real.exp (((sky g a₀:ℝ)-(sky g a:ℝ))*t):ℂ)*(due g a q b h k t x y-due g a r b h k t x y):=by
  simp only [GraphRevenue.due,service,GraphAffine.original,GraphPrices.read g q cq.grade,GraphPrices.read g r cr.grade]
  rw [GraphAnchor.converted g q b (sky g a₀) (sky g a),GraphAnchor.converted g r b (sky g a₀) (sky g a)]
  ring

theorem funded (a a₀:Fin n→Ordinary.Label (B g))(p:FLog g.core n)(q r:Ordinary.Price (B g) n)
    (loan:Ordinary.ExteriorExpansion (B g) (read g) a₀ (GraphPrices.entered g p))
    (cq:Ordinary.ExteriorExpansion (B g) (read g) a q)(cr:Ordinary.ExteriorExpansion (B g) (read g) a r)
    (K:Set (Points n))(ck:IsCompact K)(sep:K⊆conf n)(b:Fin m→Ordinary.Label (B g))
    (E:Set (Points m))(ce:IsCompact E)(ext:E⊆Outside m)(h k:ℕ):
    Rain (rate g a₀ h) (fun (i:K×E)(t:ℝ)=>due g a₀ (GraphPrices.entered g (service g p q r)) b h k t i.1.val i.2.val):=by
  have earlier:=paid g a₀ _ loan K ck sep b E ce ext h k
  have left:=paid g a q cq K ck sep b E ce ext h k
  have right:=paid g a r cr K ck sep b E ce ext h k
  simp_rw [account g a a₀ p q r cq cr]
  exact earlier.plus (GraphRevenue.change g a a₀ h (left.minus right))
end IssuedMaxwell.GraphResidual
end
