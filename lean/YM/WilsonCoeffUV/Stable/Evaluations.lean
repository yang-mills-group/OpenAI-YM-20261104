import YM.WilsonCoeffUV.Stable.PayPolynomial
/-!
# Resonant polynomial extraction costs. Later row-output ℓ1. Requested extra reserve explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k u:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X Z D':ℝ}
def feeF (n:ℕ)(p:Leg G): Prop:= ∃ C:ℝ,0≤ C ∧∀ x,‖p x‖≤ C*liftCost n x.1
lemma feeF.pays (n:ℕ)(p:Place.Potential G)(hv:p∈rangeLt _ n) : feeF n (assay p):=by
   obtain ⟨C,h,H⟩:= royalties n _ hv; refine ⟨‖(coatC G).symm.toContinuousLinearMap‖*C,by positivity,fun x=>?_⟩
   let L:G.Color→L[ℝ] Lawn G.ColorIndex:= (coatC G).symm.toContinuousLinearMap
   let u:= feather x; let a:= verdict p x.1 u.2; exact le_trans (norm_le_pi_norm (L a) x.2.2) ((L.le_opNorm a).trans ((mul_le_mul_of_nonneg_left (H x.1 u.2) (norm_nonneg _)).trans_eq (by ring)))
lemma cress (n:Fin r→ℕ)(b:Fin r→ Leg G)(p:∀ i,feeF (n i) (b i))(V:Type*)[NormedAddCommGroup V][NormedSpace ℝ V] :∃ C:ℝ,0≤C∧ ∀ (P:ChamberTen G V r)(A:ℝ), Fruit 0 1 (∑ i,n i) P A → SumBudget (fun i=>‖pressOn P b i‖) (C*A):=by
   choose B hb hv using p; let C:= ∏ i,B i; have hc:0≤C:= Finset.prod_nonneg fun i _=>hb _
   have hh y: ‖∏ i,b i (y i)‖≤ C*hedge 0 1 (∑ i,n i) y:= by
       unfold C hedge autumn; rw [norm_prod,one_mul,←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]; refine Finset.prod_le_prod (fun _ _=> norm_nonneg _) fun i _=> (hv _ _).trans ?_
       apply mul_le_mul_of_nonneg_left _ (hb i); unfold liftCost; gcongr; exact port_size ..
   refine ⟨C,hc,fun V A h=>?_⟩; apply budget_minor (cap_scale h hc) (fun i=>norm_nonneg _) (fun i=>?_); rw [pressOn,norm_smul]; exact (mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _)).trans_eq (by ring)
private lemma raised (n:Fin (r+1)→ℕ)(i:Fin (r+1)): ∑ j,Function.update n i (n i+1) j= (∑ j,n j)+1:=by
    let v:=Function.update n i (n i+1); rw [←Finset.add_sum_erase Finset.univ v (Finset.mem_univ i), ← Finset.add_sum_erase Finset.univ n (Finset.mem_univ i), show v i=n i+1 from Function.update_self ..]; rw [show (∑ j∈ Finset.univ.erase i,v j)= _ from Finset.sum_congr rfl fun j hj=> (show v j=n j from Function.update_of_ne (Finset.mem_erase.mp hj).1 ..)]; abel
lemma pruneF (i: Fin (r+1))(f: E4→ G.Color)(n:Fin (r+1)→ℕ)(p:f∈rangeLt _ (n i+1))(g:Fin (r+1)→ Leg G)(hp:∀ i,feeF (n i) (g i))(hk:(∑ j,n j)+1≤u) (V:Type*)[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]:
    ∃ C:ℝ,0≤ C∧∀ (s:ℝ),0<s →∀ (P:ChamberTen G V (r+1))(B T:ℝ), Twig 0 s T P → Smooth P→ Gale 0 1 u P B→ ‖pluck P (Function.update g i (assay (Place.jump f)))‖≤C*B:=by
    let v (x:Cover)(j:G.ColorIndex):= - f (Place.seat x) j
    let Q : Fin (r+1)→ Leg G:= Function.update g i (fun y=> v y.1 y.2.2); let R:= Function.update g i (assay (Place.jump f)); let F:= Function.update n i (n i+1)
    have he : ∀ i,feeF (F i) (Q i):= by
       intro j; unfold F Q; by_cases h:j=i; swap; · rw [Function.update_of_ne h,Function.update_of_ne h]; exact hp _
       subst j; rw [Function.update_self,Function.update_self]; obtain ⟨M,m,H⟩:= Place.band_growth p
       let L:G.Color→L[ℝ] Lawn G.ColorIndex:= (coatC G).symm.toContinuousLinearMap
       have hm:0≤‖L‖:= norm_nonneg L
       refine ⟨‖L‖*M,by positivity,fun x=>?_⟩
       unfold v; rw [norm_neg]; let y:=x.1; let B:=f (Place.seat y); apply (norm_le_pi_norm (L B) x.2.2).trans
       apply (L.le_opNorm B).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (H (Place.seat x.1)).trans; apply mul_le_mul_of_nonneg_left _ m; unfold liftCost; gcongr; exact shade_seat _
    have ht : ∀ i,Wages (R i):= run_q (fun i=>⟨_,hp i⟩) (pays_assay _ (Place.jump_band p)) i
    obtain ⟨C,hc,hh⟩:=cress F Q he V; let L:ℝ:= Fintype.card (G.ColorIndex×Axis); have hL:0≤ L:=by unfold L; positivity
    refine ⟨C*L,by positivity,fun s h0 P B T U q hx=>?_⟩
    let Z:=ledger P i; have hk:= hh Z (L*B) ((beam_r P hx i zero_le_one).slice zero_le_one (by unfold F; rw [raised]; exact hk))
    rw [show pluck _ _= -(pluck Z Q) from ?h,norm_neg]; exact (norm_tsum_le_tsum_norm hk.2.1).trans (hk.2.2.trans_eq (by ring))
    case h=>
      apply eyeY i (pressOn P R) (pressOn Z Q) ((pluck_profit U h0 ht).of_norm) hk.2.1.of_norm
      intro t; cases isEmpty_or_nonempty (YForest G); · simp
      next he' =>
       let Y:= ∏ j∈Finset.univ.erase i,g j (enlist i (Classical.arbitrary (YForest G)) t j)
       let A x j:= Y*v x j; let K:=visitJ (YForest G) i
       have hA z:(∏ j∈Finset.univ.erase i,g j (enlist i z t j))=Y:= Finset.prod_congr rfl (fun j hj=> congr_arg (g j) (remote (Finset.mem_erase.mp hj).1 t z (Classical.arbitrary _)))
       have hz (P:ChamberTen G V (r+1)) z: pressOn P Q (enlist i z t)=A z.1 z.2.2 • P (enlist i z t):=by unfold Q; rw [run_p,hA,enlist_it,mul_comm]
       apply tally2 i q A t _ _ ((K.summable_iff.mpr (pluck_profit U h0 ht).of_norm).prod_factor t) ((K.summable_iff.mpr hk.2.1.of_norm).prod_factor t) _ (hz Z) (((K.summable_iff.mpr (pluck_profit U h0 (show ∀ i,Wages (Q i) from fun i=> ⟨_,he i⟩)).of_norm).prod_factor t).congr (hz P))
       intro x j d; change pressOn P R (enlist i (waive x d j) t)=_; unfold R; rw [run_p,hA,enlist_it]; congr 1; unfold assay jump A v; simp only [Place.seat_add,Place.seat_step,waive,feather_at];
       change (f (Place.seat x) j-f (Place.seat x+basis d) j)*Y=_; ring
lemma inquest (F:Labels.Frame G h)(H:Hol G)(v: Fin r→ Place.Potential G)(n:Fin r→ℕ)(W:Multiset Axis)(hv:∀ i,v i∈ rangeLt _ (n i))(hk:(∑ i,n i)+W.card≤k)(he:k≤h)(D:ℕ)(h':h<u):
    ∃ C:ℝ, 0≤ C∧ ∀ (s:ℝ)(P:ChamberTen G (Vote D) r)(A M:ℝ), 0<s→ Twig 0 s A P→mural P→Smooth P→ Hears F k M P→ VectorWind 0 1 u M P→ ‖pluck P (assay ∘ v) (wallope W D)‖≤C*M:=by
    have hp i: n i ≤ h:= le_trans (Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)) (le_trans (Nat.le_add_right _ _) (hk.trans he))
    choose w Y hw hY hF using fun i=>Place.generated (v i) (hv i) (hp i)
    let R (i:ℕ): Fin r→Leg G:= fun j=>if j.val< i then assay (v j) else assay (sampled (Y j))
    have hh :∀ i≤ r,∃ C:ℝ,0≤ C∧∀ (s:ℝ)(P:ChamberTen G (Vote D) r)(A M:ℝ), 0<s→ Twig 0 s A P→mural P→Smooth P→ Hears F k M P→ VectorWind 0 1 u M P→‖pluck P (R i) (wallope W D)‖≤C*M:=by
       intro i; induction i with
       | zero =>
          intro _; obtain ⟨C,hc,h⟩:= poly_pressural H F Y n W he hk hY D
          exact ⟨C,hc,fun s P A M hs q u ht hg _=> by rw [show R 0=(fun i=>assay (sampled (Y i))) from funext fun i=>if_neg (Nat.not_lt_zero _)]; exact h s A M _ hg hs q u ht⟩
       | succ i ih =>
          intro z; obtain ⟨A,hA,h⟩:= ih (by omega); clear ih; cases r with
          | zero=> omega
          | succ r =>
            let t: Fin (r+1):=⟨i,z⟩
            have hg : ∀ j,feeF (n j) (R i j):=by
               intro j; unfold R; split; exact feeF.pays _ _ (hv _); exact feeF.pays _ _ (through_sample _ (hY _))
            obtain ⟨X,hX,hp⟩:= pruneF t (w t) n (hw t) (R i) hg (show (∑ i,n i)+1 ≤ u from by omega) (Vote D)
            let d:=wallope W D
            refine ⟨X*‖d‖+A,by positivity,fun s P B M h0 q u g e ht=>?_⟩
            have heq: R (i+1)=Function.update (R i) t (assay (v t)):=by
               funext j; by_cases hx:j=t; · subst j; unfold R; rw [Function.update_self,if_pos]; exact Nat.lt_succ_self _
               rw [Function.update_of_ne hx]; unfold R; simp only [show j.val< i+1 ↔ j.val< i from by have he:j.val≠i:= fun h=>hx (Fin.ext h); omega]
            have htq: assay (v t)-R i t= assay (Place.jump (w t)):=by unfold R; rw [if_neg (show ¬ t.val< i from lt_irrefl i),hF,assay_add,add_sub_cancel_right]
            let J:=pluck P (R (i+1))-pluck P (R i)
            have hy : ‖J‖ ≤ X*M:=by unfold J; rw [heq,pluck_grade q h0 (fun j=>⟨_,hg j⟩) (pays_assay _ (hv t)),htq]; exact hp s h0 P M B q g ht
            rw [show pluck P (R (i+1))=J+pluck P (R i) from (sub_add_cancel ..).symm,_root_.add_apply]; exact (norm_add_le ..).trans ((add_le_add ((J.le_opNorm d).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))) (h s P B M h0 q u g e ht)).trans_eq (by ring))
    specialize hh r le_rfl; rw [show R r= assay ∘ v from funext fun i=> if_pos i.isLt] at hh; exact hh
lemma gateway (H:Hol G)(F:Labels.Frame G h)(v:Fin r→ℕ)(W:Multiset Axis)(hk:(∑ i,v i)+W.card≤k)(p:k≤h)(D:ℕ)(h':h<u): ∃ C:ℝ, 0≤C∧∀ (s:ℝ)(P:ChamberTen G (Vote D) r)(A M:ℝ), 0<s→Twig 0 s A P→ mural P→Smooth P→ Hears F k M P→VectorWind 0 1 u M P → ∀(f: Fin r→ Place.Potential G), (∀ i,f i∈ rangeLt _ (v i))→
    ‖pluck P (assay ∘ f) (wallope W D)‖ ≤ C*M*(∏ i,slideRank (v i) (f i)):=by
   let B i:= Module.finBasis ℝ (Jury G (v i)); let Y (i):= Fin (Module.finrank ℝ (Jury G (v i)))
   let V i (j:Y i):= (B i j).val
   have hv (i j): V i j∈ rangeLt (Axis→G.Color) (v i):= (B i j).property
   choose C hc hx using fun b : (i:Fin r)→ Y i=> inquest F H (fun i=> V i (b i)) v W (fun i=> hv i (b i)) hk p D h'
   choose T ht H' using fun i=> cog G (v i)
   refine ⟨∑ b,(∏ i,T i)*C b,Finset.sum_nonneg (fun i _=> mul_nonneg (Finset.prod_nonneg fun _ _=> ht _) (hc _)),fun s P A M ha q u e z a f g=> ?_⟩
   let d:=wallope W D; let x i: Jury G (v i):= ⟨f i,g i⟩; let c (i):= (B i).equivFun (x i)
   let Q i (j:Y i):= c i j • assay (V i j)
   have hq i j: Wages (Q i j):= pays_assay _ (Submodule.smul_mem (rangeLt _ (v i)) (c i j) (hv i j))
   have he i: assay (f i) = ∑ j,Q i j:=by
       let L: Jury G (v i)→ₗ[ℝ] Leg G := {
           toFun z:= assay z.val
           map_add' _ _:=rfl
           map_smul' _ _:= rfl }
       change L (x i)=_; conv_lhs=>rw [← (B i).sum_repr (x i),map_sum]
       apply Finset.sum_congr rfl; intro j _; rw [map_smul]; rfl
   have hg i j : ‖c i j‖≤ T i*slideRank (v i) (f i):= le_trans (norm_le_pi_norm (c i) j) (H' i _)
   rw [show assay∘f=fun i=>∑ j,Q i j from funext he,gathers P Q hq q ha,_root_.sum_apply]; simp_rw [Finset.sum_mul]
   refine le_trans (norm_sum_le ..) (Finset.sum_le_sum (fun b _=>?_)); unfold Q; rw [graded,_root_.smul_apply,norm_smul];
   rw [norm_prod]; refine (mul_le_mul (Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> hg i _)) (hx b s P A M ha q u e z a) (norm_nonneg _) (Finset.prod_nonneg (fun i _=> mul_nonneg (ht _) (slide_nn ..)))).trans_eq ?_; rw [Finset.prod_mul_distrib]; ring
end YM.WilsonCoeffUV.Shard
