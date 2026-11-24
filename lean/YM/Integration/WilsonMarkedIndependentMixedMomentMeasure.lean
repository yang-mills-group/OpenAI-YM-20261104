import YM.Integration.WilsonMarkedIndependentMixedMomentProduct

/-! Exponentially small differences on the full signed test return, retaining
the same proper log faces before every multiplication and child test. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedMomentMeasure
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Shard WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open Source Source.Drops Labels
open WilsonMarkedIndependentMixedMomentTensor (Tensor logged)
open WilsonMarkedIndependentPhysicalIntake (PairedAt)
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]{D:ι→ℕ}{m e:ℕ}{n:ℕ→Side}{t:ℕ→ℝ}

theorem measured {u y:ℝ}{k:ι→ℕ}(F:Garland D)(z:CellR)(Y:ℕ→Outerm G D){s B:ℝ}
    (growth:Tendsto (fun p=>(n p).val) atTop atTop)(width:0<s)(budget:1≤B)
    (old:∀ᶠp:ℕ in atTop,∀N,m≤N → PairedAt e (Y N) (n p) s B):
    Tensor G ℝ m e n (fun p=>catchW s (n p)) (fun N=>Finale u y z F k (AuthSum (Y N))):=by
  apply WilsonMarkedIndependentMixedMomentTensor.sum _ _ (fun p=>catch_hot s (n p))
  intro x _
  apply WilsonMarkedIndependentMixedMomentTensor.smul
  let A:=touch (lyra u y z F x) univ
  have aligned:=WilsonMarkedIndependentMixedMomentProduct.moment (G:=G) (m:=m) (e:=e) (n:=n)
    (fun N=>Y N x) (fun p=>catch_hot s (n p)) univ
    (fun J _=>logged growth width budget old x J)
  intro i hi r v
  exact WilsonMarkedIndependentMixedMomentPrice.mapped A (aligned i hi r v)

theorem agree {U:Type}[NormedAddCommGroup U]{Y Z:ℕ→Era G U}
    (same:∀N,m≤N → Y N=Z N)(funds:Tensor G U m e n t Y):Tensor G U m e n t Z:=by
  intro i hi r x
  obtain ⟨C,cp,old⟩:=funds i hi r x
  refine ⟨C,cp,?_⟩
  filter_upwards [old] with p rows
  intro N cut
  rw [←same N cut]
  exact rows N cut

end YM.Integration.WilsonMarkedIndependentMixedMomentMeasure
end
