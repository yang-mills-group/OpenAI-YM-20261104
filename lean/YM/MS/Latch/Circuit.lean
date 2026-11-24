import YM.MS.Latch.Country
/-!
# Anchor join in a tree shell. Uses offset of first relative second; scalar reanchoring not needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal
open scoped Topology ContDiff
variable {G:Gauge}{b c: Bool}{s t h:ℤ} {ι E F J:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F]{S:Scale ι}{n d:ℕ}{x y a z v:ι→ℝ}{A:ι→QP}{X Y:ι→ Law G}{K:ι→ Edge G}
local notation "Ψ"=> field ( Landau.parity ( A:=Axis ) (C:=G.ColorIndex))
def meshZ (P:Edge G)(i j:BH G)(F H:Law G)(l r:Legs (Lane4 G))(q:QP): ℂ:= 2*P i j q*(cross ( parity j ) ( degree Ψ l ) * F ((i,q)::l))* H ((j,-q)::r)
def Cabin (A:QP)(P:Edge G)(μ:Measure QP)(F H:Law G) : Law G:= fun w=> scatter Ψ w (fun l r=>Tone.bill A ( net l )*(∑ i:BH G,∑ j:BH G,∫ q,Tone.bill A q * meshZ P i j F H l r q ∂μ))
variable {w l r:Wire (BH G) E QP}{μ:ι→Measure QP}
abbrev Qbud (w:Wire (BH G) E QP)(s:Scale ι)(u:ι→ℝ):= (fun i=>s.length i^pitch w*u i)
abbrev packMesh (i j:BH G)(K:ι→Edge G)(X Y:ι→Law G)(l r:Wire (BH G) E QP) (s:ι)(q:QP× E):= meshZ (K s) i j (X s) (Y s) (sail l q.2) (sail r q.2) q.1
def Centroid (w:ι→ℝ): Prop:=∀ i,0< w i
lemma meshC (h:Sheet S a K)(i j:BH G)(hl:Split l r w)(hx: Lease false true S X x)(hy:Lease false true S Y y): pole S ( packMesh i j K X Y l r ) ( Qbud w S ( positive S 4 a (x*y) ) ) := by
   let u:= ContinuousLinearMap.fst ℝ QP E; let L:=Wire.lift l (ContinuousLinearMap.snd ℝ QP E); let R:=Wire.lift r (ContinuousLinearMap.snd ℝ QP E); let q:= (i,u):: L; let z:=(j,-u)::R; let a' :ℂ:=2*cross (parity j) (degree (field parity) l)
   obtain hp := hx (QP× E) q (fun c=> Bool.noConfusion c) (fun _=>by simp [q]); obtain hr := hy (QP× E) z (fun c=> Bool.noConfusion c) (fun _=> by simp [z]) ; have he : Bound S (fun i w=>Plane.Chart X q i w* Plane.Chart Y z i w) (fun i=> S.length i^ pitch q*x i*( S.length i^pitch z*y i)):= Costs.mul hp hr; obtain hu := ( h i j|>.rapid (F:=E) ).mul he; convert hu.L (ContinuousLinearMap.mul ℝ ℂ a') using 1
   · funext k p; unfold packMesh meshZ; rw [sail_degree]; rcases p with ⟨v,w⟩; simp only [Plane.Chart,q,z,sail_cons,lift_sail,u,L,R,_root_.neg_apply, ContinuousLinearMap.mul_apply']; unfold a'; ring_nf; rfl
   funext k; unfold Qbud;  unfold q z L R positive pitch; simp only [field_cons,field_lift]; obtain hz:=split_sum (wfield ∘ Prod.fst) hl; change fieldDim wfield l+fieldDim wfield r=fieldDim wfield w at hz;
   calc
      _ = S.length k ^ ( (4:ℤ)+fieldDim wfield w ) * (a k*(x k*y k)):= by rw [zpow_add₀ (S.pos _).ne']; rw [Pi.mul_apply,show S.length k^(4:ℤ)= S.length k^(4:ℕ) from rfl]; ring
      _ = _:= by rw [show (4:ℤ) + fieldDim wfield w=(4-wfield i-wfield j)+(wfield i+fieldDim wfield l)+(wfield j+fieldDim wfield r) from (by omega),zpow_add₀ (S.pos _).ne', zpow_add₀ (S.pos _).ne']; ring
-- abstraction for lifting Osc stats. Only mark joins anchored. Meter T includes bound property for period later. Lease positive.
lemma cab_cost (hv:∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ l r w:Wire (BH G) E QP,Split l r w→ Bound S (fun i p=> Tone.bill (A i) (net l p)* (∑ j:BH G,∑ k:BH G,Fiddle.quoteF A μ (packMesh j k K X Y l r) i p)) ( Qbud w S v )): Lease false false S (fun i=> Cabin ( A i ) (K i) (μ i) (X i) (Y i)) v := by
    intro E _ _ w hw he; unfold Cape Plane.Chart Cabin; simp_rw [sail_scatter,sail_net]; exact gather_bound w (fun l r H=>hv E l r w H)
section
-- regular μ integral
variable (hk:Sheet S a K)(hx:Lease false true S X x)(hy:Lease false true S Y y)(ha:nn a)(hL:nn x)(hR:nn y)
include hk hx hy ha hL hR
abbrev Hob (_S:Scale ι)(a x y:ι→ℝ):= a*(x*y)
lemma hob (H:glob S μ d)(hp:Mint S μ d) (hv:∀ (E:Type)[ NormedAddCommGroup E][ NormedSpace ℝ E ], S.full.Le (fun i (_:E)=>‖A i‖) ( fun i _=> S.length i )): Lease false false S (fun i=> Cabin (A i) (K i) (μ i) (X i) (Y i)) (a*(x*y)):= by
   refine cab_cost (fun E _ _ l r w hW=>?_); apply pulse_bill (net l) _ (hv E); refine Costs.sum _ (fun i _=> Costs.sum _ (fun j _=>?_) ?h0) ?h0; swap; · exact fun i _ _=> pos_nn _ (joy ha (joy hL hR)) S i
   apply Costs.raise ( Wavepay (fun i=> sailor ( A i )) H (meshC hk i j hW hx hy) (hp E)); apply Cost.of_le; intro t p _; apply le_of_eq; unfold Qbud positive Snap.fee; simp only [ Pi.mul_apply]; field_simp [(S.pos t).ne']
-- small distance separation substantial.All-order power.R factor. To absorb.We choose s separation min; x y a; amplitude.M
lemma pulseB (hb:∀ i,0<v i)(hA:∀ i,v i≤ ‖A i‖)(ht:∀ i,S.length i≤v i)
    (hc:∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E], S.full.Le (fun i (_:E)=>‖A i‖) (fun i _=>v i))(k:ℕ): Lease false false S (fun i=> Cabin ( A i ) (K i) planeF (X i) (Y i)) (fun i=> a i*(x i*y i)*( S.length i/v i)^k ) := by
   let c i:= S.length i/v i; have hv i:0<c i:= div_pos ( S.pos i ) (hb i); have hz i:c i≤1:= ( div_le_one (hb i)).mpr (ht i);
   refine cab_cost (μ:=fun (_:ι)=>planeF) (fun E _ _ l r w hW=>?_); let U i:= S.length i ^ pitch w*(a i*(x i*y i)); rw [ show Qbud w S _=(fun i=>U i*c i^k) from funext fun i=> (mul_assoc ..).symm]; refine pulseCost (net l) (g:=fun i (_:E)=>U i) ?_ hv hz ?_ k; swap; · unfold c; convert hc E using 1; ext i; field_simp [(S.pos i).ne',(hb i).ne'] -- patch
   intro k; refine Costs.sum _ (fun i _=> Costs.sum _ (fun j _=>?_) ?h0) ?h0; swap; · exact fun i _ _=>mul_nonneg ( pos_nn _ (joy ha (joy hL hR)) S i ) ( pow_nonneg (hv i|>.le) _)
   have hh := large hb hA ( fun i=>by simpa using ht i) zero_le_one (meshC hk i j hW hx hy) k; apply Costs.raise hh (Cost.of_le fun i w' _=>?_); unfold Qbud c positive Snap.fee U; simp only [ Pi.mul_apply]; apply le_of_eq; field_simp [(S.pos i).ne',(hb i).ne']
end
end YM.MS.Latch
