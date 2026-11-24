import YM.OPE.Compatible.Gems.Buffs
/-! # Card.Near footprint budgets single exposures. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T) (Y:Studio L)
local notation "Fθ"=> L.ForestQ
noncomputable abbrev νMom:=Chart.tangent G (Y.X:Type)
local notation "μ"=>Y.μφ
abbrev Drive (L:Host K T):= Vθ L.Z L.ForestQ G
noncomputable abbrev LitA (L:Host K T)(w:L.DirA)(i:Drive L):=castAt (MintS L.Z L.ForestQ G) i w -- Fθ notation issue
noncomputable abbrev Vlamp (x:Y.St):= Y.V (Y.boat x)
noncomputable abbrev PulseP (i:Drive L)(x:Y.St):ℝ:= LitA L (Vlamp L Y x) i
noncomputable abbrev Vtone (i:Y.St):= (Vlamp L Y i).2
lemma breezeY (x:L.DirA)(i:Key L.ForestQ G) : LitA L x (Sum.inr i)=cash (Limn.Tip G (forest L.Z.ratio L.H).Free) x.2 i:=by
       change cash (MintS L.Z Fθ G) x (Sum.inr i)=_; unfold cash MintS; rw [Module.Basis.equivFun_apply,Module.Basis.prod_repr_inr]; rfl -- names
lemma azWorld (i:Wings G L.c)(x:Y.St):PulseP L Y (Sum.inl i) x=cash (JetB G L.c) Y.w i:=by
       change cash (MintS L.Z Fθ G) (Vlamp L Y x) (Sum.inl i)=_; unfold cash MintS; rw [Module.Basis.equivFun_apply,Module.Basis.prod_repr_inl];rfl
lemma leftZ (x:Y.St): Vtone L Y x= Vtone L Y 0+stake Y.X x:=by unfold Vtone Vlamp Studio.boat Studio.V VegaP; dsimp only; rw [map_add,zero_add]; abel
lemma tagT (i: Key L.ForestQ G) (x:Y.St) : PulseP L Y (.inr i) x= PulseP L Y (.inr i) 0 + (if h:i.1∈Y.X then axY L Y (⟨_,h⟩,i.2) x else 0):=by
       rw [PulseP,PulseP,breezeY,breezeY]; let T:=Limn.Tip G (forest L.Z.ratio L.H).Free; change cash T (Vtone L Y x) i=_; rw [leftZ, Tip_ψ,Tip_ψ]; change _+(stake Y.X x i.1) i.2= _; congr 1; split
       next ht=> erw [stake_on Y.X (⟨_,ht⟩:↥Y.X)]; exact Eq.symm (Tip_ψ (((⟨i.1,ht⟩):↥Y.X),i.2) x)
       next ht=>rw [stake_off Y.X x i.1 ht];rfl
end
end YM.OPE.Borealis.Galea
