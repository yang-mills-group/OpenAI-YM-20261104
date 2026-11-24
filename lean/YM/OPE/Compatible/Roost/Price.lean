import YM.OPE.Compatible.Roost.Hol
/-! # Sea.Boot -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b u:ℝ}(A:Alps K T i v){D:Alps K T j v'} {U:Boxes G P' K.K}
local notation "Y!"=>solar G d τ
local notation "T!"=> Tracts G d τ
open JetS
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}
variable (H hs) (t:Town A D U R u)(h: Aware d τ) (hi:4 ≤ i)(hj:4 ≤ j)(ha:0 ≤ v)(hb:0 ≤ v')
set_option maxHeartbeats 200000 in
lemma turnG (e k:ℕ) (V: Even c.val)(x y:Site c)(hx: Pins K P x y)(p q:solar G d τ)(J:Phase)(a:Axis)(he:P'.L=P.L^m)(hw:e+e<k)(hW:∀ i,Rise.stamp' d G k+44 ≤τ i):
    let T:= yankV D t H hs h; Thick (lapPrice P.L e*lapPrice P.L e) (fun i=> Variance.HillP A H hi hs ha P x y V a J (i+m) p q- Variance.HillP D H hj hs hb P x y V a J i (T p) (T q)) :=by
       intro T; apply Variance.polyZ _ (EndFare P.L k) _ (badge (P:=P) (Nat.lt_succ_self _) _ hw); obtain ⟨v',hX,ht⟩:= hx; let W:Type:={ i:ℕ // barrier P' ≤ (CountL c P.L i).val}; let n(i:W):=CountL c P.L i.val; let R':=Visite t W; let K'(i:W):=χ' (K:=K) (n i) P'; have V'(i:W):Even (n i).val:= evenBoot K P V i.val; let X(i:W):=spikeS K P x i.val; let Y(i:W):= spikeS K P y i.val; let g:=actor A U R 0 ⟨hs,H,t.eph⟩ h
       have hp' :∀ i:W, ‖R'.chant hs H h i‖ ≤ ‖g‖:=fun _=>le_refl _; have ht':=R'.beacon V' (fun i=>i.property) hi hj hs (fun _=>ha) (fun _=>hb) H h (temp' t hb _ W) ⟨_,hp'⟩ X Y v' hX (fun i=>ht _) hW J
       let f(i:W):Dice (solar G d τ):= ArmZ A ((K' i).embed (X i)) ((K' i).embed (Y i)) (even_both (K' i) (V' i)) hs hi H ha J; let M(i:W):Dice (solar G d τ):=ArmZ D (X i) (Y i) (V' i) hs hj H hb J; let p':=spose a G d τ p; have he'(i:W): Variance.HillP D H hj hs hb P x y V a J i.val (T p) (T q)=pullD T (M i) p' q:=by
           change M i (spose a G d τ (T p)) (T q)= M i (T p') (T q); rw [show T p'= spose a G d τ (T p) from sun_marks hs H h a t _]
       obtain ⟨b,hb,F'⟩:= ht'; refine ⟨ b*(c.val:ℝ)⁻¹^k*‖p'‖*‖q‖,?_⟩; filter_upwards [(Variance.enoughAway P c).eventually (eventually_ge_atTop (barrier P'))] with i hI; let j:W:=⟨i,hI⟩; let R0:=f j-pullD T (M j); let N:ℝ:=(n j).val; have hh: ‖‖R0‖‖ ≤ b*N^0 * (((CountL c P.L i).val:ℝ)⁻¹^k):= F' j; rw [Real.norm_of_nonneg (norm_nonneg R0), pow_zero,mul_one,hostV] at hh; rw [raising A H hs hi ha V x y p q J a i he, show Variance.HillP D H hj hs _ P x y V a J i _ _=_ from he' j]; change ‖R0 p' q‖≤_ ; apply (InvokeB ..).trans; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (norm_nonneg _)) (norm_nonneg _)).trans_eq (by unfold lapPrice;ring)
open Topic
lemma portGrowth (V:Even c.val)(x y:Site c)(he:P'.L=P.L^m)(hx:Pins K P x y)(a:Axis)(p q:Tracts G d τ)(J:Phase)(hp:k > l+l)(hW:∀ i,Rise.stamp' d G k+44 ≤ τ i):
     let F := MotionX (A:=A) H hs t D₀.aware hi hj; let G:=Topic.PhaseP (D₀:=D₀) (H:=H) (hs:=hs) A hi ha a x y V J; let T:=PhaseP (D₀:=D₀) (H:=H) (hs:=hs) D hj hb a x y V J; Thick (lapPrice P.L l*lapPrice P.L l) (fun i=>G (i+m) p q-T i (F p) (F q)):=by
        intro f g x₀; let s:=Fallix G D₀.aware K A.gear hi; let v:=Fallix G D₀.aware K D.gear hj; let Z:= yankV D t H hs D₀.aware; have hz(p):v (f p)=Z (s p):= v.apply_symm_apply _; change Thick _ (fun i=>g (i+m) p q-Variance.HillP _ _ _ _ _ _ _ _ _ _ _ i (v (f p)) (v (f q))); rw [hz p,hz q]; exact turnG A H hs t D₀.aware hi hj ha hb l k V x y hx _ _ J a he hp hW
end YM.OPE.Stroke
