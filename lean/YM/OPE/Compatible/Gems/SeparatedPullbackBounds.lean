import YM.OPE.Compatible.Gems.Veer
/-! # Paired vertical pull.Hushing.Y.Vale -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R ε:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T)(Y:Studio L) (w: Bid.Dir G L.c)
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "φY"=> axisEquiv
local notation "L!"=> majr L
noncomputable abbrev yQ (p:Y.St →ℝ):= p ∘ ViewS L Y
local notation "Γ!"=> Chart.tangent G (forest L.Z.ratio L.H).Free
variable {p:Y.St→ℝ}
lemma y_cost {A:price}(h:Cane Y.μφ p A): Cane (majr L) (yQ L Y p) A:=fun i hi=>Reprice _ (Γ!) _ _ (ViewS L Y) (shutt L Y) (h i hi)
noncomputable abbrev TagK (i:Drive L):= yQ L Y (PulseP L Y i)
lemma Morn (z:AxisChart G L.ForestQ)(i:Rubric G Y.X): TagK L Y (Sum.inr (shout G Y.X i)) z = LitA L (stareD L Y.w z) (Sum.inr (shout G Y.X i))+ Δp Y.X L.F.L.Q i (z+L.F.L.M Y.w-Y.ext):=by
        unfold TagK yQ PulseP Function.comp; simp only; rw [breezeY,breezeY]; let X:= Y.X; let v:=shout G X i; let V:= cash (Limn.Tip G (forest L.Z.ratio L.H).Free); let p:= L.F.L.M Y.w; let B:= Y.boat (ViewS L Y z); let s:= Y.ext; let K:= stake Y.X (G:=G); have hh: B= ViewS L Y (z+p-s):=by unfold B Studio.boat; rw [show Y.centerA= _ from (show Y.centerA= ViewS L Y (p-s) from rfl),← map_add]; congr 1;abel
        let H:=cash (Limn.Tip G (Y.X:Type)); change V (s+K B) v=V (p+z) v+(H (ViewS L Y (z+p-s)) i-V (z+p-s) v); rw [←hh]; have hv : V (K B) v= H B i:=by unfold V H; rw [Tip_ψ, Tip_ψ]; rw [show ((K B) v.1)= B i.1 from stake_on Y.X i.1 B];rfl
        simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply,hv];ring
abbrev quiet (i:Rubric G Y.X)(t:ℝ):Prop:=∀ j:Wings G L.c, cash (JetB G L.c) Y.w j≠cash (JetB G L.c) w j→ t ≤ separation (pointK L.Z Fθ (shout G Y.X i)) (cotW L.Z j)
variable {L Y w}
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t)(hw:‖w‖≤ t)
include h ht hc he
lemma bulk_F : Next.SectorChange.Schur.Pours (LiftM L.Z L.H L.A L.k L.U) (pointK L.Z Fθ) (cotW L.Z) (u/2) (flowerC G s u c C):=by
        obtain ⟨p,H⟩:=h.stem; exact RegularM _ _ _ _ _ h.signed ht hc he H (by omega) h.vein
include hv hw
lemma Marine (x:AxisChart G L.ForestQ)(i:Rubric G Y.X)(hh: quiet L Y w i ℓ) :
       let j:= Sum.inr (shout G Y.X i)
       ‖LitA L (stareD L Y.w x) j-LitA L (stareD L w x) j‖ ≤ Real.exp (-(u/2*ℓ))*(flowerC G s u c C)*(2*t):=by
           intro i'; let Q:= Limn.Tip G (forest L.Z.ratio L.H).Free; let H:= L.F.L.M; let v:=Y.w; let j:= shout G Y.X i; let f:= JetB G L.c; let D:= LiftM L.Z L.H L.A L.k L.U; let T:= cash Q; have hz(y): T (H y)= D*ᵥ cash f y:= Rvoice _ _ _ _ L.k L.F h.signed _; rw [breezeY,breezeY]; change ‖T (H v+x) j-T (H w+x) j‖≤ _
           simp only [map_add, Pi.add_apply,add_sub_add_right_eq_sub,hz]; let g(i:Wings G L.c):Prop:=cash f v i≠cash f w i; let U(i):= cash f v i; let W(i):= cash f w i
           change ‖(D *ᵥ U) j-(D *ᵥ W) j‖≤ _; rw [mulVec,mulVec,dotProduct,dotProduct, ←Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans; have hV:= CoverSlip g (half_pos h.vein.warmth) (bulk_F h ht hc he) j hh -- warm u/2
           have ht:0 ≤ t:=(norm_nonneg _).trans hw; apply le_trans _ (mul_le_mul_of_nonneg_right hV (show 0 ≤ 2*t by positivity)); rw [sum_mul]; apply Finset.sum_le_sum; intro i _; rw [←mul_sub,norm_mul]; split
           · exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans ((add_le_add ((Cast_price v _).trans hv.w) ((Cast_price w _).trans hw)).trans_eq (by ring))) (norm_nonneg _)
           next he=> rw [show U i=W i from Classical.not_not.mp he,sub_self,norm_zero,zero_mul,mul_zero]
end
end YM.OPE.Borealis.Galea
