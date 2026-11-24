import YM.WilsonCoeffUV.Root.Gain.Charges
/-! Per fine-vertex pressure estimate. Before choosing the beacon L.
Ages all V packets released earlier to *post* scarcity.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X Z D':ℝ}
lemma rung (F:Labels.Frame G h)(H:Hol G) (i: Fin r→Fin (h+2))(b: Chunk h)(e:h<D)(C:ℝ)(hs:0<s)(ht:0<t):
    ∃ T:ℝ,0≤ T∧∀ (P:Patch)(w:Site P.L)(Q:Drip P G)(x:Fin r→YForest G)(Y:ChamberTen G (Vote D) r)(A M:ℝ)(f:Scroll D), Crank Q (h+1) s C→ r*(s/P.L.val)≤ t/2 → Smooth Y→ mural Y→ Twig 0 t A Y→ Wing 0 t M Y→ Hears F h M Y →
       ‖pluck Y (fun j=> splint P Q w (x j) (h+1) (i j)) (jotC P w f b)‖≤ (T*(A*speck P^(h+1)+M))*Real.exp (-s*port_d 0 x)*‖page D f‖:=by
   by_cases H0 : h+1≤mMarked i+rateC b
   · obtain ⟨L,hL,h⟩:= portion_rug G D h r i C s t hs ht
     obtain ⟨c,hc,hf⟩:= chunk_prep b e
     refine ⟨L*c,by positivity,fun P w Q x Y A M f g p a u t0 v z=>?_⟩
     have hp := h P Q w x Y A g p t0; let S:= speck P; have hS : 0<S:= speck_pos P; set K:= Real.exp (-s*port_d 0 x); have hk : 0≤ K:=by unfold K; positivity;
     have ha:=t0.1; have he:=z.fair; apply ((pluck Y _).le_opNorm (jotC P w f b)).trans; refine (mul_le_mul hp (hf P w f) (norm_nonneg _) (by positivity [speck_pos P])).trans ?_
     rw [show _ * K * (c* (_ * ‖page D f‖))= L*c*(A*S^(mMarked i+rateC b))*K*‖page D f‖ from by unfold S; ring]; gcongr; exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hS.le (speck_le P) H0) ha).trans (le_add_of_nonneg_right he)
   cases b with
   | none => simp only [rateC] at H0; omega
   | some b=>
      obtain ⟨T,hT,hg⟩:= tumbles F H i b (show mMarked i+b.val.card≤h from Nat.le_of_lt_succ (Nat.lt_of_not_ge H0)) D s C hs ht
      refine ⟨T,hT,fun P w Q x Y A M f g t0 a u p v y=>?_⟩; have hz := y.fair; have hx:= p.1; have hp:= speck_pos P
      have ht: ‖halo P w b.val f‖ ≤ ‖page D f‖:= (halo_bound P w f b.val (le_trans b.property e.le)).trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hp.le (speck_le _)))
      rw [jotC,map_smul,norm_smul,mul_comm]; exact mul_le_mul ((hg P w Q x Y A M g a u p v y).trans (by gcongr; apply le_add_of_nonneg_left (by positivity))) ht (norm_nonneg _) (by positivity)
private def ringStar (x:Cover):Equiv.Perm (YForest G):= Equiv.prodCongr (Equiv.addLeft x) (Equiv.refl _)
def featherS (P:Patch)(w:Site P.L)(Y:ChamberTen G (Vote D) r) : ChamberTen G (Vote D) r:= (soprano P w D) ∘ revolve (lift w) Y
def pulseS (P:Patch)(w:Site P.L)(Q:Drip P G)(Y:ChamberTen G (Vote D) r): ChamberTen G (Vote D) r:= pump (featherS P w Y) (owns P.L Q)
lemma pulse_dress (P:Patch)(w:Site P.L)(Q:Drip P G)(g:Crank Q k s X)(Y:ChamberTen G (Vote D) r)(p:Twig 0 t A Y)(ht:0<t)(hp:0<s) (x:Fin r→YForest G): pulseS P w Q Y x= soprano P w D (pluck Y (fun i=> sip P Q w (x i))):=by
   let F i:= sip P Q w (x i); have hf i: Wages (F i):=by unfold F; rw [sipping P Q w (x i) k]; exact Wages.sums (fun j _=> splints P Q w (x i) g hp j)
   let T:= ((Equiv.refl (Fin r)).arrowCongr (ringStar (G:=G) (lift w)))
   rw [pluck,(soprano P w D).map_tsum (pluck_profit p ht hf).of_norm,pulseS,pump, ← T.tsum_eq]; apply tsum_congr; intro y
   unfold spinJob featherS; rw [Function.comp_apply, revolve, pressOn,map_smul]; congr 2; rw [show jog (-lift w) ∘ T y=y from ?_]
   funext i; rcases he:y i with ⟨b,d⟩; simp [T,ringStar,jog, he]
lemma pulse_pay (F:Labels.Frame G h)(H:Hol G) (r:ℕ)(e:h<D)(C:ℝ)(hs:0<s)(ht:0<t):
    ∃ T:ℝ,0≤ T∧∀ (P:Patch)(w:Site P.L)(Q:Drip P G)(Y:ChamberTen G (Vote D) r)(A M:ℝ), Crank Q (h+1) s C→ r *(s/P.L.val)≤t/2 → Smooth Y→ mural Y→ Twig 0 t A Y→ Wing 0 t M Y→ Hears F h M Y →
       Twig 0 s (T*(A*speck P^(h+1)+M)) (pulseS P w Q Y):=by
    choose T hT h' using fun (i:Fin r→Fin (h+2))(b:Chunk h)=> rung F H i b e C hs ht
    let V:= ∑ i,∑ b,T i b; have hv:0≤V:= Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> hT _ _
    refine ⟨V,hv,fun P w Q Y A M g p a u q v z=>?_⟩; let S:= A*speck P^(h+1)+ M; have hh:= z.fair; have hS : 0≤ S:= by unfold S; have H:= q.1; positivity [speck_pos P]
    refine ⟨mul_nonneg hv hS,fun x=>?_⟩; set K := Real.exp (-s*port_d 0 x); have hk : 0≤ K:=by unfold K; positivity
    apply ContinuousLinearMap.opNorm_le_bound _ (show 0≤ V*S*K by positivity); intro c
    obtain ⟨f,rfl⟩:= submitted c; rw [pulse_dress P w Q g Y q ht hs]; let R i j:=splint P Q w (x i) (h+1) j
    rw [show (fun i=>sip P Q w (x i))=fun i=>∑ b,R i b from funext fun i=> sipping P Q w (x i) _, gathers Y R (fun i=>splints P Q w (x i) g hs) q ht]; change ‖(∑ i:Fin r→Fin (h+2), pluck Y (fun j=> R j (i j))) (foldWord P w D (page D f))‖≤ _
    rw [chunks P w f h,_root_.sum_apply]; simp_rw [map_sum]
    unfold V; simp_rw [Finset.sum_mul]; apply (norm_sum_le ..).trans; exact Finset.sum_le_sum fun i _=> (norm_sum_le ..).trans (Finset.sum_le_sum (fun b _=> h' i b P w Q x Y A M f g p a u q v z))
end YM.WilsonCoeffUV.Cosmos
