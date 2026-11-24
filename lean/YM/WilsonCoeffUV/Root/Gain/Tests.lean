import YM.WilsonCoeffUV.Root.Gain.Polynomial
/-! Wage wind plume per polynomial, covers exact m and all tail units. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X Z D':ℝ}

-- Convenient update/folds.
section
variable [NormedAddCommGroup V][NormedSpace ℝ V] {P:ChamberTen G V r}{b d:Fin r→ Leg G}{q t:Leg G}
lemma run_p {v:Leg G}(y:Fin r→YForest G)(i:Fin r): pressOn P (Function.update b i v) y=(v (y i)* ∏ j∈Finset.univ.erase i,b j (y j)) • P y:=by
    unfold pressOn; rw [update_prod _ i,Function.update_self]; congr 2; exact Finset.prod_congr rfl fun j hj=>congr_fun (Function.update_of_ne (Finset.mem_erase.mp hj).1 ..) _
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma run_q (g:∀ i,Wages (b i))(x:Wages q)(i:Fin r): ∀ j,Wages ((Function.update b i q) j):=by
   intro j; by_cases h:j=i; · rw [h,Function.update_self]; exact x
   rw [Function.update_of_ne h]; exact g _
variable [CompleteSpace V]
lemma pluck_minus (h:Twig 0 s A P)(hp:0<s)(g:∀ i,Wages (b i))(x:Wages q)(y:Wages t)(i): pluck P (Function.update b i (q-t))=pluck P (Function.update b i q)-pluck P (Function.update b i t):= by
    unfold pluck; rw [← (pluck_profit h hp (run_q g x i)).of_norm.tsum_sub ((pluck_profit h hp (run_q g y i)).of_norm)]; apply tsum_congr; intro y; simp_rw [run_p,Pi.sub_apply,sub_mul,sub_smul]
lemma pluck_grade (h:Twig 0 s A P)(hp:0<s)(g:∀ i,Wages (b i))(x:Wages q)(i): pluck P (Function.update b i q)-pluck P b=pluck P (Function.update b i (q-b i)):=by rw [pluck_minus h hp g x (g i), Function.update_eq_self]
-- q-t axis and U for tally
lemma pluck_gradient (i: Fin (r+1))(f: E4→ G.Color)(p:f∈rangeLt _ k)(g:Fin (r+1)→ Leg G)(hp:∀ i,Wages (g i))(h0:0<s)(V:Type*)[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]:
    ∃ C:ℝ,0≤ C∧∀ (P:ChamberTen G V (r+1))(B T:ℝ), Twig 0 s T P → Smooth P→ roaring 0 P s B→ ‖pluck P (Function.update g i (assay (Place.jump f)))‖≤C*B:=by
    let v (x:Cover)(j:G.ColorIndex):= - f (Place.seat x) j
    let Q : Fin (r+1)→ Leg G:= Function.update g i (fun y=> v y.1 y.2.2); let R:= Function.update g i (assay (Place.jump f))
    have he : ∀ i,Wages (Q i):= by
       apply run_q hp; obtain ⟨M,m,H⟩:= Place.band_growth p
       let L:G.Color→L[ℝ] Lawn G.ColorIndex:= (coatC G).symm.toContinuousLinearMap
       have hm:0≤‖L‖:= norm_nonneg L
       refine ⟨k,‖L‖*M,by positivity,fun x=>?_⟩
       unfold v; rw [norm_neg]; let y:=x.1; let B:=f (Place.seat y); apply (norm_le_pi_norm (L B) x.2.2).trans
       apply (L.le_opNorm B).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (H (Place.seat x.1)).trans; apply mul_le_mul_of_nonneg_left _ m; unfold liftCost; gcongr; exact shade_seat _
    have ht : ∀ i,Wages (R i):= run_q hp (pays_assay _ (Place.jump_band (grows G.Color (Nat.le_succ k) p))) i
    obtain ⟨C,hc,hh⟩:=upon Q he h0 V; refine ⟨C,hc,fun P B T u q hx=>?_⟩
    let F:=ledger P i; have hk:= hh F B (ledger_stencil hx i)
    rw [show pluck _ _= -(pluck F Q) from ?h,norm_neg]; exact (norm_tsum_le_tsum_norm hk.2.1).trans hk.2.2
    case h=>
      apply eyeY i (pressOn P R) (pressOn F Q) ((pluck_profit u h0 ht).of_norm) hk.2.1.of_norm
      intro t; cases isEmpty_or_nonempty (YForest G); · simp
      next he' =>
       let Y:= ∏ j∈Finset.univ.erase i,g j (enlist i (Classical.arbitrary (YForest G)) t j)
       let U x j:= Y*v x j; let K:=visitJ (YForest G) i
       have hA z:(∏ j∈Finset.univ.erase i,g j (enlist i z t j))=Y:= Finset.prod_congr rfl (fun j hj=> congr_arg (g j) (remote (Finset.mem_erase.mp hj).1 t z (Classical.arbitrary _)))
       have hz (P:ChamberTen G V (r+1)) z: pressOn P Q (enlist i z t)=U z.1 z.2.2 • P (enlist i z t):=by unfold Q; rw [run_p,hA,enlist_it,mul_comm]
       apply tally2 i q U t _ _ ((K.summable_iff.mpr (pluck_profit u h0 ht).of_norm).prod_factor t) ((K.summable_iff.mpr hk.2.1.of_norm).prod_factor t) _ (hz F) (((K.summable_iff.mpr (pluck_profit u h0 he).of_norm).prod_factor t).congr (hz P))
       intro x j d; change pressOn P R (enlist i (waive x d j) t)=_; unfold R; rw [run_p,hA,enlist_it]; congr 1; unfold assay jump U v; simp only [Place.seat_add,Place.seat_step,waive,feather_at];
       change (f (Place.seat x) j-f (Place.seat x+basis d) j)*Y=_; ring
end
-- R=0 for vacuum unit: claw as universally quantified r equation

def Wing {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](o:Cover)(s A:ℝ): {r:ℕ}→ChamberTen G E r → Prop
   | 0,_=> 0≤A
   | _+1,P=> roaring o P s A
lemma Wing.pn {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{o: Cover}{P:ChamberTen G E r}(hp: Wing o s A P): 0≤A:=by cases r; exact hp; exact (show roaring _ _ _ _ from hp).1
lemma Wing.cap {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{o:Cover}{P:ChamberTen G E r}(hp:Wing o s A P)(e:A≤X): Wing o s X P:=by cases r; exact hp.pn.trans e; exact ⟨hp.pn.trans e,fun x j=> ((show roaring _ _ _ _ from hp).2 x j).le e⟩
-- each fixed wage n and polynomial v
lemma suture (F:Labels.Frame G h)(H:Hol G)(v: Fin r→ Place.Potential G)(n:Fin r→ℕ)(W:Multiset Axis)(hv:∀ i,v i∈ rangeLt _ (n i))(hk:(∑ i,n i)+W.card≤k)(he:k≤h)(D:ℕ)(h0:0<s):
    ∃ C:ℝ, 0≤ C∧ ∀ (P:ChamberTen G (Vote D) r)(A M:ℝ), Twig 0 s A P→mural P→Smooth P→ Hears F k M P→ Wing 0 s M P→ ‖pluck P (assay ∘ v) (wallope W D)‖≤C*M:=by
    have hp i: n i ≤ h:= le_trans (Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)) (le_trans (Nat.le_add_right _ _) (hk.trans he))
    choose w Y hw hY hF using fun i=>Place.generated (v i) (hv i) (hp i)
    let R (i:ℕ): Fin r→Leg G:= fun j=>if j.val< i then assay (v j) else assay (sampled (Y j))
    have hh :∀ i≤ r,∃ C:ℝ,0≤ C∧∀ (P:ChamberTen G (Vote D) r)(A M:ℝ), Twig 0 s A P→mural P→Smooth P→ Hears F k M P→ Wing 0 s M P→‖pluck P (R i) (wallope W D)‖≤C*M:=by
       intro i; induction i with
       | zero =>
          intro _; obtain ⟨C,hc,h⟩:= poly_pressural H F Y n W he hk hY D
          exact ⟨C,hc,fun P A M q u ht hg _=> by rw [show R 0=(fun i=>assay (sampled (Y i))) from funext fun i=>if_neg (Nat.not_lt_zero _)]; exact h s A M _ hg h0 q u ht⟩
       | succ i ih =>
          intro z; obtain ⟨A,hA,h⟩:= ih (by omega); clear ih; cases r with
          | zero=> omega
          | succ r =>
            let t: Fin (r+1):=⟨i,z⟩
            have hg : ∀ j,Wages (R i j):=by
               intro j; unfold R; split; exact pays_assay _ (hv _); exact pays_assay _ (through_sample _ (hY _))
            obtain ⟨X,hX,hp⟩:= pluck_gradient t (w t) (hw t) (R i) hg h0 (Vote D)
            let d:=wallope W D
            refine ⟨X*‖d‖+A,by positivity,fun P B M q u g e ht=>?_⟩
            have heq: R (i+1)=Function.update (R i) t (assay (v t)):=by
               funext j; by_cases hx:j=t; · subst j; unfold R; rw [Function.update_self,if_pos]; exact Nat.lt_succ_self _
               rw [Function.update_of_ne hx]; unfold R; simp only [show j.val< i+1 ↔ j.val< i from by have he:j.val≠i:= fun h=>hx (Fin.ext h); omega]
            have htq: assay (v t)-R i t= assay (Place.jump (w t)):=by unfold R; rw [if_neg (show ¬ t.val< i from lt_irrefl i),hF,assay_add,add_sub_cancel_right]
            let J:=pluck P (R (i+1))-pluck P (R i)
            have hy : ‖J‖ ≤ X*M:=by unfold J; rw [heq,pluck_grade q h0 hg (pays_assay _ (hv t)),htq]; exact hp P M B q g ht
            rw [show pluck P (R (i+1))=J+pluck P (R i) from (sub_add_cancel ..).symm,_root_.add_apply]; exact (norm_add_le ..).trans ((add_le_add ((J.le_opNorm d).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))) (h P B M q u g e ht)).trans_eq (by ring))
    specialize hh r le_rfl; rw [show R r= assay ∘ v from funext fun i=> if_pos i.isLt] at hh; exact hh
-- cumulant upgrade later by gauges/path atom columns.
end YM.WilsonCoeffUV.Cosmos
