import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.OrthogonalShell
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ColorJets
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Filtered
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Sectors
open YM YM.Maxwell YM.Extra.FD
variable {G:Gauge}

theorem color (u:G.El)(A:Labels.Jet G):
    reroute (Labels.colored u A)=stain u (reroute A):=by
  funext i
  change asSol (takeCurl (Labels.Taylor.paint u (A i)))=
    actionG u i (asSol (takeCurl (A i)))
  rw [IssuedMaxwell.ColorJets.curl,IssuedMaxwell.OrthogonalShell.original]
  rfl

theorem acquired (d:ℕ)(p:WickPol G):
    p∈LinearMap.range (observable G d) ↔ p∈through G d ∧ secret p:=by
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨IssuedMaxwell.Filtered.reduce w.property.1,?_⟩
    intro u V
    change probe (stain u V) (reduceEq w.val)=probe V (reduceEq w.val)
    rw [jet_value,jet_value]
    have h:(fun i=>gaugeJet (stain u V i))=Labels.colored u (fun i=>gaugeJet (V i)):=by
      funext i
      exact IssuedMaxwell.ColorJets.original u (V i)
    rw [h]
    exact w.property.2 (fun i=>gaugeJet (V i)) u
  · rintro ⟨cap,fixed⟩
    obtain ⟨limit,back⟩:=IssuedMaxwell.Filtered.original cap
    refine ⟨⟨writeRaw p,limit,?_⟩,back⟩
    intro A u
    rw [writeRaw_read,writeRaw_read,color]
    exact fixed u (reroute A)

theorem original (g:YangMills.GaugeGroup)(d:ℕ)(p:WickPol g.core):
    p∈LinearMap.range (observable g.core d) ↔
      (IssuedMaxwell.Shell.coordinates g).Admissible d p:=
  (acquired d p).trans (IssuedMaxwell.SectorSpine.admissible g d p).symm
end IssuedMaxwell.Sectors
end
