import YM.OPE.Compatible.Hatch.Birth
/-! # Cost transport into orthogonal cube. Projection preserves Hardy plateau. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
set_option maxHeartbeats 200000
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
open Aloof
namespace Sleeve
variable {I:Type}{A:I→ Side}{φ:Filter I}{Z:I→ℝ}{W:I→ℕ}{a c b':ℝ}(U:Scaffold φ Z A W r)
variable (q p: GlyphQ G A)
open Scaffold
variable (h:Shor U q p)(V:(i:I)→Board (A i) (r+1))
-- Application to arbitrary enactments. Costs independent of input size using Roster.G.
open Cinders
variable {D:I→ Type} [∀ i, MeasurableSpace (D i)] {μ:(i:I)→Measure (D i)}[∀ i,IsProbabilityMeasure (μ i)]
variable (X:(i:I)→D i→ Bid.Dir G (A i)) (Y:(i:I)→D i→ Chamber G r)
noncomputable abbrev TossK (k:ℕ) (i:I)(z:D i):= OpX (Article q (k+1)) V i (X i z) (Y i z)
variable (hX:SkinQ A Z μ φ X)(hY: SkyQ r Z μ φ a Y) (ha:a ≤ 0)
noncomputable def Rtax (i:I)(z:D i):=Roster (X i z)+‖Y i z‖+1
include hX hY
omit [∀ i, IsProbabilityMeasure (μ i)] in lemma agentV (k:ℕ): ∀ᶠ i in φ, Measurable (TossK q V X Y k i):=by
        filter_upwards [hY.aug,hX.meat] with i hi hv; let H:=sailT G (V i); let f:= Article q (k+1) i; have hp:Measurable f:= (show Bond f from tallJ (k+1) (q i) 0).smooth.continuous.measurable; have ht:Measurable (fallS V Y i):=by
            change Measurable ((sailT G (V i)) ∘ Y i); with_reducible_and_instances exact (sailT G (V i)).measurable.comp hi
        have he: TossK q V X Y k i=(f∘ (X i+fallS V Y i))-(f∘ X i):=by
             funext v; unfold TossK OpX; simp only [Pi.sub_apply,Function.comp_apply,Pi.add_apply,fallS]; rfl
        rw [he]; exact (hp.comp (hv.add ht)).sub (hp.comp hv)
include ha h
lemma rentZ (k:ℕ): Grain μ φ Z (TossK q V X Y k) a:=by
       obtain ⟨t,ht,H⟩:= JFair U q p h V k; let f:=Rtax X Y; let v:=U.top.fair; have hp: Grain μ φ Z f 0:=((hX.Φ.add (hY.leg.mint ha) v).add (Grain.const (RateLE.const 1 v)) v); apply Grain.of_le ((((Grain.const ht).mul (hp.pow v k)).mul hY.leg).mint (by simp)) ((agentV q V X Y hX hY k).mono fun i hi=> hi.aestronglyMeasurable); filter_upwards[H] with i hi; filter_upwards with x; let b:=X i x; let c:= Y i x; exact (hi b c (f i x) (add_pos_of_nonneg_of_pos (add_nonneg (ros _) (norm_nonneg _)) zero_lt_one) (le_add_of_nonneg_right zero_le_one)).trans (Real.le_norm_self _)
lemma rentL (k:ℕ): Grain μ φ Z (fun i z=> TossK q V X Y k i z-TossK q V (HopPI A W X) Y k i z) c:= by
       obtain ⟨t,ht,H⟩:= JAnchor (a:=c) U q p h V k; let S:=HopPI A W X; have hz:=agentV q V X Y hX hY k; have he:=agentV q V S Y (hX.Rise X) hY k; let f:=Rtax X Y; let v:=U.top.fair; let T:= hY.leg.mint ha; have hp: Grain μ φ Z f 0:=((hX.Φ.add T v).add (Grain.const (RateLE.const 1 v)) v); apply Grain.of_le ((((Grain.const ht).mul (hp.pow v k)).mul T).mint (by simp)) ((hz.and he).mono fun i hi=> (hi.1.sub hi.2).aestronglyMeasurable); filter_upwards [H] with i hi; filter_upwards with z; exact (hi _ _ (f i z) (add_pos_of_nonneg_of_pos (add_nonneg (ros _) (norm_nonneg _)) zero_lt_one) (le_add_of_nonneg_right zero_le_one)).trans (Real.le_norm_self _)
-- ∆ shift. projection δ takes extra leap; h_Z scale. f full−sill error.L.
variable (L:I→Law (Chamber G r))(R:GlyphQ G A)(p':GlyphQ G A)
section
local notation "WZ_F"=> Coach R V X L
local notation "X_F"=> HopPI A W X
local notation "W_K"=>Coach R V (X_F) L
noncomputable abbrev CDelta:= Chair R V X L-Chair R V (HopPI A W X) L
noncomputable abbrev TCoach : (i:I)→D i→ Bid.Dir G (A i):= HopPI A W (Coach R V X L)
include U in omit hY ha h hX [∀ i, IsProbabilityMeasure (μ i)][∀ i,MeasurableSpace (D i)] in lemma marchD (i:I)(x:D i) : Coach R V (HopPI A W X) L i x= (TCoach (W:=W) V X L R i x)+fallS V (CDelta (W:=W) V X L R) i x:=by
        let z:= X i x; let H:= sailT G (V i); let T:=pour H (chrom (R i)) (L i); let K:= Cpit G A W i; have he(y):K (H y)=H y:=Sill_sail (V i) y (U.top.room i).wide
        unfold Coach TCoach HopPI Coach fallS CDelta Chair; simp only [mate,_root_.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply]; with_reducible_and_instances change K z-H (T (K z))= K (z-H (T z))+ H (T z-T (K z)); rw[map_sub,he,H.map_sub]; abel
variable (hR: Shor U R p')(hc:∀ i,SiteL (sailT G (V i)) (chrom (R i)) (L i))
variable {δ:ℝ} (hv:0<δ)(hL:∀ i x,δ*‖x‖^2 ≤ (L i).P x x)
include hc hv hL hR
omit h hY hX ha hv hL hR hc [∀ i, IsProbabilityMeasure (μ i)][∀ i,MeasurableSpace (D i)] in
include U in lemma Φstep (k:ℕ)(i:I)(z:D i): let Q:=Coach R V X L; let K:=Coach R V (X_F) L; let M:=CDelta (W:=W) V X L R; let T:=TCoach (W:=W) V X L R; let P:=TossK q V; P Q Y k i z-P T Y k i z - (P (T+fallS V Y) M k i z-P T M k i z)=P Q Y k i z-P K Y k i z:=by
       intro Q K M T F; dsimp only [K,Q,F]
       let E:= Article q (k+1) i; let x:=Coach R V X L i z; let b:= Y i z; let P:=sailT G (V i); let D:= M i z; let a:= T i z; let c:=P D; have he:Coach R V (HopPI A W X) L i z=a+c:= by have hZ:= marchD U V X L R i z; unfold fallS at hZ; with_reducible_and_instances exact hZ
       unfold TossK OpX; rw [he]; simp only [Pi.add_apply,fallS]; with_reducible_and_instances change ((E (x+P b)-E x)-(E (a+P b)-E a))-((E ((a+P b)+c)-E (a+P b)) - (E (a+c)-E a)) = (E (x+P b) - E x) - (E ((a+c)+P b)-E (a+c)); rw [add_right_comm a (P b)]; abel
lemma rentD (k:ℕ)(hc':c ≤ 0): Grain μ φ Z (fun i z=> TossK q V (Coach R V X L) Y k i z-TossK q V (Coach R V (HopPI A W X) L) Y k i z) c:=by
       let Q:= WZ_F; let T:=TCoach (W:=W) V X L R; have ht:=TourP U R p' hR V X hX L hc hv hL; let M:=CDelta (W:=W) V X L R; have hM: SkyQ r Z μ φ c M:=TourDiff U R p' hR V X hX L hc hv hL
       let τ:=T+fallS V Y; have hh: SkinQ A Z μ φ T:=ht.Rise _; have hz: SkinQ A Z μ φ τ:= hh.roos _ ((hY.live Y ha).turns V _) U.top.fair; let f':= rentL (c:=c) U q p h V (Coach R V X L) Y ht hY ha k; let v':=U.top.fair; apply Grain.shift (f'.sub ((rentZ U q p h V τ M hz hM hc' k).sub (rentZ U q p h V T M hh hM hc' k) v') v'); filter_upwards with i; ext1 z
       with_reducible_and_instances exact Φstep (U:=U) q V X Y L R k i z
end
end Sleeve
end YM.OPE.Merchant
