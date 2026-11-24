import YM.WilsonCoeffUV.Winding.Mark
import YM.WilsonCoeffUV.Reclosure.Paths.WindingAlias
/-!
# Monetary alias gaps off actual unmasked representations at ONE STEP
Meant before alignment (so same-origin MR equality after germ algebras).
Mark comparison local in complete span of TRUE chosen roots, not to ad hoc
nonminimal lift of a torus kernel. Winding that goes around between two marks
could be very short on the torus and unobservable on cover. Aliasing/cutting
in retained hull is meaningful, as well as at all admissible torus sizes for
unmarked anchored and single-mark outputs.
-/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Cosmos Mer Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets PowerSeries Bank.Mosaic Bank.Carp
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type}{G:Gauge}{D k:ι→ℕ}{i j r e a l:ℕ}{s A B C W t q :ℝ}
variable {J Z S:Finset ι}{p:ι→Cover}

lemma quarry {F:X→V}[NormedAddCommGroup V][CompleteSpace V]{a:X}{c:X→ℝ}(_h:Summable (fun y=> ‖F y‖))(p: SumBudget c C)(v:∀ i,i≠a→ ‖F i‖ ≤ c i):
     ‖(∑' i,F i)- F a‖ ≤ C:=by
    classical
    let Y (i:X):= if i=a then 0 else F i; have he:SumBudget (fun i=> ‖Y i‖) C:=budget_minor p (fun _=> norm_nonneg _) (fun i=> by unfold Y; by_cases hi:i=a; rw [if_pos hi,norm_zero]; exact p.1 i; rw [if_neg hi]; exact v i hi)
    let u (i:X):= if i=a then F a else 0; have ht:HasSum u (F a):= by
        convert (hasSum_single (f:=u) a (fun i hi=>if_neg hi)) using 1
        rw [show u a=F a from if_pos rfl]
    rw [show F=u+Y from funext (fun i=>by by_cases hi:i=a <;> simp [u,Y,hi]), show tsum (u+Y)=(∑' i,u i)+ tsum Y from ht.summable.tsum_add he.2.1.of_norm]; simp only [Pi.add_apply]; rw [ht.tsum_eq,show u a=F a from if_pos rfl,show Y a=0 from if_pos rfl,add_zero,add_sub_cancel_left]; exact (norm_tsum_le_tsum_norm he.2.1).trans he.2.2

lemma splice_half {u i:ℕ}(p:u ≤ 2*i)(h:0≤s): 1≤ catchW (s/2) u * Real.exp (s*i) := by
    unfold catchW; rw [← Real.exp_add]; apply Real.one_le_exp; have hu:(u:ℝ)≤ 2*i:=by exact_mod_cast p
    nlinarith

abbrev perchA (s:ℝ)(t:ℕ):= min s (hingeZ s t/2)
lemma perch_pos (p:0<s)(i:ℕ): 0<perchA s i:=lt_min p (div_pos (hinge_paid p i) (by norm_num))
lemma bridgeA {F:post G i}(h:Amber Bank.terrain s A F)(p:0<s)(v:stroll F):
    Sight (lagoon F n) F (perchA s i) (A*(hinges s i+1)):=by
    let w:=hingeZ s i; let E:= A*hinges s i; let B:=A*(hinges s i+1); have he : E ≤ B:=by unfold B E; have hh:= h.1; gcongr; linarith
    have g:A ≤ B:=le_mul_of_one_le_right h.1 (le_add_of_nonneg_left (hinge_reserve p i).le); have hg:0<w:= hinge_paid p i
    let L' := lagoon F n; have hp: Amber (tor n) (perchA s i) (A*hinges s i) L':= (lagoon_cost h p n).mono (min_le_right ..)
    refine ⟨by rw [pruce_down]; exact hp.le he,(h.mono (min_le_left ..)).le g, ⟨h.1.trans g,fun x b=> ?_⟩,lagoon_walk F n⟩; rw [pruce_down]; let X:=slideC n x; let R:=flair X F; have hz:R (salvo x)= F x:=by
        unfold R; rw [flair_hit (sole_right x),plantern]; refine (congr_arg F ?_).trans (v (-(x 0).1) x); ext1 i; refine Prod.ext ?_ rfl; change feetP _ _= -(x 0).1+_; rw [sole_salvo,sub_eq_add_neg,add_comm]
    have hu:= flair_cost h p X
    have hv: Summable (fun i=>‖R i‖):=(hu.unweighted hg.le).2.1
    let t:= catchW (w/2) n; have ht:0≤t:= catch_hot ..; have hT : t*E ≤ B*catchW (perchA s i) n:= by rw [mul_comm]; exact mul_le_mul he (catch_width (min_le_right ..) n) ht (h.1.trans g)
    change ‖(∑' i,R i)-F x‖≤_; rw [←hz]; refine (quarry hv (cap_scale (by exact hu) ht) ?_).trans hT
    intro a u; by_cases e: trope X a
    · have he:n.val≤ 2*size a:=by
          apply Nat.le_of_not_gt; intro g; apply u; funext ⟨i,j⟩; have h : lift (wrap n ((x i.succ).1 - (x 0).1))= lift (wrap n (feetP a i.succ)):= by rw [map_sub]; exact congr_arg lift (e i.succ)
          have hg:= leg_le Bank.terrain (Prod.fst ∘ x) 0 i.succ; rw [map_sub, nearTau (by change Bank.terrain.gap (x 0).1 (x i.succ).1≤ soar Bank.terrain x at hg; omega)] at h
          have H:= measure_foot a i.succ; rw [size_centers n (feetP a i.succ) le_rfl (by omega),feetP,Fin.cons_succ] at h; exact congr_fun h.symm j
      change _≤t*(Real.exp (w*size a)* ‖R a‖); rw [←mul_assoc]; exact le_mul_of_one_le_left (norm_nonneg _) (splice_half he hg.le)
    change ‖R a‖≤ t* (Real.exp (w*size a)* ‖R a‖); rw [show R a=0 from flair_miss e]; simp

variable [NormedAddCommGroup V]
lemma coast (p:ι→Cover)(J: Finset ι)(x:dock Cover α i) : Syn (tor n) (wrap n ∘ p) J (slideC n x)≤ Syn Bank.terrain p J x:=by
   unfold Syn; rw [foyer_fold]; let V:= foyer p J x; have hv(y z:Cover): (tor n).gap (wrap n y) (wrap n z)≤ Bank.terrain.gap y z:=by unfold Bank.terrain tor; dsimp only; rw [←map_sub]; exact wrap_size ..
   apply league_le (tor n); intro i j; exact (hv (V i) (V j)).trans (leg_le Bank.terrain V _ _)
open Classical in
lemma plumeW [Fintype α][CompleteSpace V]{F:Ten V (Cloth α) i}(p': Wig Bank.terrain p s A J F)(v:J.Nonempty)(h:0<s) :
 MarkU p J (Bank.Carp.plume F n) F (s/32) ((priceM α i s + tiePay α i (s/4) + 1)*A):=by
    obtain ⟨k,hk⟩:=v; let p0:=p k; have he:s/32<s:=by linarith
    set t:= s/32; have ht:0<t:=by unfold t; positivity
    let u:=tiePay α i (s-s/32); let v:=tiePay α i (s/4); let z:=boardPay α (Winding.tailC i (s/4))^i; let B:=(priceM α i s+v+1)*A; have hu:0≤u:=tie_non (sub_pos.mpr he); have hv:0≤v:=tie_non (by positivity); have hx:0≤ z:= pow_nonneg (boardPay_nn (tail_good i (by positivity))) _
    have ha:=p'.1; have hg:A≤B:=by change A≤(u+2*z+v+1)*A; nlinarith
    have hh:u*A ≤ B:=by change _≤ (u+2*z+v+1)*A; nlinarith
    have hH(y:dock Cover α i)(j):Bank.terrain.gap p0 (y j).1≤ Syn Bank.terrain p J y :=leg_le Bank.terrain (foyer p J y) (.inl ⟨k,hk⟩) (.inr j)
    have hX(y:dock (Site n) α i): SumBudget (fun i=> ‖peglet F n y i‖) (A*Real.exp (-t*Syn (tor n) (wrap n ∘ p) J y)*u) := by
         cases i with
         | zero=>
             refine ⟨fun _=>norm_nonneg _,summable_of_hasFiniteSupport (Set.toFinite _),?_⟩; rw [tsum_fintype,Fintype.sum_unique]
             rw [peglet,if_pos (Subsingleton.elim ..),show u=1 from pow_zero _,mul_one]; apply (p'.shave he.le).2 default |>.trans
             rw [← show slideC n (default:dock Cover α 0)=y from Subsingleton.elim ..]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (coast ..)) (by linarith))) ha
         | succ i=>
             have hl:0<(s-t)/(i+1:ℕ):=div_pos (sub_pos.mpr he) (by positivity)
             apply budget_minor (cap_scale (train_pay hl p0 (i+1)) (mul_nonneg ha (show 0≤Real.exp _ from by positivity))) (fun _=> norm_nonneg _); intro a; change ‖peglet _ _ _ a‖ ≤ A*_*_; unfold peglet; split
             next hz=> rw [← hz,mul_assoc]; exact (p'.2 a).trans (mul_le_mul_of_nonneg_left (sail_cut (d:=Bank.terrain) (coast (n:=n) p J a) ht.le he (by omega) p0 _ (hH a)) ha)
             rw [norm_zero]; exact mul_nonneg (mul_nonneg ha (by positivity)) (sail_nn ..)
    refine ⟨(p'.shave he.le).more hg, ⟨ha.trans hg,fun y=>?_⟩, ⟨ha.trans hg,fun x b=>?_⟩⟩
    · apply (norm_tsum_le_tsum_norm (hX y).2.1).trans; apply (hX y).2.2.trans; rw [mul_right_comm,mul_comm A u]; exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    let W:= peglet F n (slideC n x); have hp:W x=F x:=by unfold W peglet; rw [if_pos rfl]
    let c:= catchW t n; have hc:0≤ c:= catch_hot ..; have hK:z*A≤ B:=by change z*A ≤ (u+2*z+v+1)*A; nlinarith
    have hl :A*c*z ≤ B*c:=by rw [mul_right_comm,mul_comm A z]; exact mul_le_mul_of_nonneg_right hK hc
    change ‖tsum W-_‖≤_; rw [←hp]; refine (quarry (hX (slideC n x)).2.1 (cap_scale (train_pay (tail_good i (show 0<s/4 from by positivity)) p0 i) (mul_nonneg ha hc)) ?_).trans hl
    intro y g; change ‖W y‖≤_; unfold W peglet; split; swap; · rw [norm_zero]; exact mul_nonneg (mul_nonneg ha hc) (sail_nn ..)
    rename_i m; have hm : ¬4*Syn Bank.terrain p J y<n.val:=by
       intro w; have hz : unfoldAt p0 (slideC n y)=y:= unfoldReady (fun i=> vn (hH y i) w); apply g; rw [m,unfoldReady (fun i=> vn (hH x i) b)] at hz; exact hz.symm
    rw [mul_assoc]; apply (p'.shave (show s/2≤s from by linarith)).2 y |>.trans
    exact mul_le_mul_of_nonneg_left ((spent_ceil (s:=s) hm h.le).trans (mul_le_mul_of_nonneg_left (sail_floor (hH y) (show 0<s/4 from by positivity)) hc)) ha
end YM.WilsonCoeffUV.Winding
