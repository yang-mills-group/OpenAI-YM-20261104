import YM.OPE.Compatible.Gems.Arch
/-! # Lantern pay. Through η constrained. -/
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
local notation "μ"=>Y.μφ
open Next.SectorChange.Schur
variable {L Y}
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)
structure Scale (Y:Studio L)(t:ℝ):Prop where
       w : ‖Y.w‖ ≤t
       v : ‖Y.ext‖≤ t
variable (hv:Scale Y t)
include h ht hc he hv
abbrev Fξ(G:Gauge)(s c u C t:ℝ):= crestPrice G (flowerC G s u c C * t)
abbrev Pξ(G:Gauge)(s c u C t:ℝ):= crestPrice G (porchPrice G u (limbC G s c) C * (Fξ G s c u C t + t))
noncomputable abbrev FWind (G:Gauge)(s c u C t:ℝ):price:= fun k=> t+Pξ G s c u C t+Real.sqrt C*ampleP k
lemma stareT : ‖Y.centerA‖ ≤ Pξ G s c u C t:=by
       let p:= L.F.L.M Y.w-Y.ext; have hL : 0 ≤ flowerC G s u c C := (by -- from lemma Drift
          obtain ⟨p,hp⟩:=h.stem; exact (RegularM L.Z L.H L.A L.U L.k h.signed ht hc he hp (by omega) h.vein).pos)
       have hp:‖p‖≤ Fξ G s c u C t+t:= (norm_sub_le ..).trans (add_le_add ((h.drift ht hc he _).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv.w hL) (Nat.cast_nonneg _))) hv.v); exact (h.ripple ht hc he _ p).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (h.PourA ht hc he Y.X).pos) (Nat.cast_nonneg _))
lemma ShiftV (i:Key Fθ G): ‖PulseP L Y (Sum.inr i) 0‖≤ t+Pξ G s c u C t:=by
       let f:= Vtone L Y 0; have hz : f=Y.ext+stake Y.X Y.centerA:=by unfold f Vtone; change Y.ext+stake Y.X (0+_) = _; rw[zero_add] -- patch
       rw [PulseP,breezeY]; apply (Cast_price f i).trans; rw [hz]; apply (norm_add_le ..).trans; rw [firmly]; exact add_le_add hv.v (stareT h ht hc he hv)
lemma TinV (i:Drive L): Cane μ (PulseP L Y i) (FWind G s c u C t):=by
       rcases i with i|i
       · rw [funext (azWorld L Y i)]; refine (Cane.constant _ ((Cast_price ..).trans hv.w)).grow ?_; intro k hk; unfold FWind; have hh:0≤ Pξ G s c u C t:= (norm_nonneg _).trans (stareT h ht hc he hv); have he:= mul_nonneg (Real.sqrt_nonneg C) (le_trans zero_le_one (le_max_left (1:ℝ) ((k.factorial:ℝ)*(2*Real.exp (1/2))))); exact (le_add_of_nonneg_right hh).trans (le_add_of_nonneg_right he)
       let v':= FWind G s c u C t; let a:= t+Pξ G s c u C t; let w:= PulseP L Y (Sum.inr i); have hp:=ShiftV h ht hc he hv i
       by_cases H:i.1∈Y.X
       · let j:Rubric G Y.X:= (⟨_,H⟩,i.2); have heP : w=(fun _=>w 0) + (⇑(axY L Y j)):= funext fun k=> by rw [show w k= _ from tagT L Y i k,dif_pos H];rfl
         change Cane μ w v'; nth_rw 1 [heP]; refine (Cane.constant _ hp).add (D:=fun k=> Real.sqrt C*ampleP k) (fun k hk=>?_); exact Lal _ _ _ (Real.sqrt_nonneg C) ((h.takeK ht hc he Y.X _).trans_eq (Real.sq_sqrt h.vein.broad.le).symm) hk
       change Cane μ w v'; have he' : w= fun _=>w 0:= funext fun x=>by rw [show w x= _ from tagT L Y i x,dif_neg H,add_zero]
       nth_rw 1 [he']; apply (Cane.constant _ hp).grow; intro i hi; exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one (le_max_left ..)))
end
end YM.OPE.Borealis.Galea
