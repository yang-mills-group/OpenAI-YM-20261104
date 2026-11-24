import YM.OPE.Compatible.Seas.Birch
/-! # Singular records. Wing loans -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
open Next.Rank.Radian (dV stroll)
open Pose (epic)
variable {s:ℝ}{f g:Cover→ℝ}{F G:E4→ℝ}{U:Gloam}{p q:Pose}{l k j:ℕ}
def Nook (l:ℕ)(f:Cover→ℝ)(F:E4→ℝ):Prop:= Quip (↑(l+2:ℕ):ℤ) f F ∧ KelvinAng l F
namespace Nook
lemma tarn : Nook l (0:Cover→ℝ) (0:E4→ℝ):=⟨fun n x h p hp ht=>by simp [quilting],ang_zero l⟩
lemma fence (hf:Nook l f F): epic F:=hf.2.diff
lemma sublet (hf:Nook l f F)(hg:Nook l g G): Nook l (f-g) (F-G):=⟨by intro n x hn p hp ht; simpa only [quilting,Pi.sub_apply, mul_sub] using! (hf.1 n x hn p hp ht).sub (hg.1 n x hn p hp ht), hf.2.sub hg.2⟩
lemma frosh (hp:Nook l f F)(a:Cover):Nook l (fun x=> f (x+a)) F:=⟨hp.1.shiftP _,hp.2⟩
lemma gnaws (p:Pose)(D:List Axis)(i:Axis):Nook (p.aLen D) (dvol D (p.icicle i)) (p.pureD D i):=by
    have he:p.aLen D+2= p.heat+1+D.length:=by unfold Pose.aLen Pose.heat;omega
    refine ⟨he ▸ p.era D i,?_⟩
    have hh(a:Axis):KelvinAng (p.aLen D) (tint (D++a::p.m)):=by rw [←p.path_len D a];let v:=p.path D a; refine ⟨gravy v,pellet _,fun x hx=>?_⟩; exact taxes hx _
    unfold Pose.pureD Pose.Lck;apply KelvinAng.sub
    · split; apply hh; exact ang_zero _
    split; apply hh; exact ang_zero _
lemma pay (hf:Nook l f F):∃ B≥0,∀ x:Cover,‖f x‖ ≤ B/(notch x:ℝ)^(l+2):=by
    obtain ⟨C,hC,H⟩:= Quip_cash hf.1; simp_rw [_root_.zpow_neg,zpow_natCast,← div_eq_mul_inv] at H; exact ⟨C,hC,H⟩
end Nook
section permits
variable {t v:ℕ→Cover→ℝ}{R:ℕ→ℕ}{d:ℝ}
lemma alone (hf:Nook l f F)(hh:Port U d k t)(hq: Crown U R)(hs:s<d)(h:∀ᶠ i in atTop,U.h i*R i ≤ s)(hz:j+4=k+(l+2)): Fruit U j (Oct R f t) 0:=by
   by_cases hx:l+2<4
   · obtain ⟨C,hC,H⟩:=hf.pay; exact brain hq (hz.trans (add_comm ..)) (show (3-(l+2))+(l+2)=3 from by omega) hh hs h hC H
   obtain ⟨m,he⟩:∃ m,l=m+2:=⟨l-2,by omega⟩
   have hp:= Nook.fence hf
   subst l
   have he:= fad hq hh hs h (k:=k) (j:=m) hf.1 hp
   rw [show j=k+m from by omega]; let s':=U.q'⁻¹; let G:=Port.eve U k m t
   suffices ht:fineI s' (F*G)=0 by erw [ht] at he; exact he
   obtain ⟨A,hA,H⟩:= hf.2; have ht:0 < s':=inv_pos.mpr (zero_lt_one.trans U.qsub); have hG:=Port.pureE U k m t
   rw [show fineI s' (F*G)=countM s' (m+1) (G*A) from ?_,ladder (show PureA (2*(m+1)) (G*A) from ?_) ht, show ends (m+1) (G*A)=0 from silence hG hA (by omega) (by omega)]; simp
   · have hp:=pure_multiply (pureE U k m t) hA.size; rw [show m+(m+2)=2*(m+1) from by omega] at hp; exact hp
   apply integral_congr_ae; filter_upwards with x; by_cases h:x=0; · subst x; rw [coldA.self_of_nhds]; simp
   simp only [Pi.mul_apply,H (show x∈away from h),Pi.pow_apply,smul_eq_mul];ring
lemma twineB {u:ℕ}(hf:Nook l f F)(hp:Nook u g G)(hh:Port U d k t)(hq:Crown U R)(hs:s<d)(h:∀ᶠ i in atTop,U.h i*R i≤s):Fruit U (k+(l+u)) (Oct R (f*g) t) (fineI U.q'⁻¹ ((F*G)*eve U k (l+u) t)):=by
    apply fad hq hh hs h ?_ (Pose.epic_m hf.fence hp.fence); rw [show ((↑(l+u+4:ℕ):ℤ))=(l+2:ℕ)+(↑(u+2:ℕ):ℤ) from by omega]; exact hf.1.purse hp.1
lemma thrice {b c:ℕ}{p:Cover→ℝ}{P:E4→ℝ}(hf:Nook l f F)(hg:Nook b g G)(hp:Nook c p P)(hp':0<d)(hn:Crown U R)(hs:s<d)(h:∀ᶠ i in atTop,U.h i*R i≤s)(he:k+4=(l+2)+(b+2)+(c+2)) : Fruit U k (fun i=> ∑ x∈pod (R i), f x*g x*p x) 0:=by
   have H : Quip (↑(k+4:ℕ):ℤ) (f*g*p) (F*G*P):=by rw [show (↑(k+4:ℕ):ℤ)= (↑(l+2:ℕ):ℤ)+(↑(b+2:ℕ):ℤ)+(↑(c+2:ℕ):ℤ) from by omega]; exact (hf.1.purse hg.1).purse hp.1
   let T:ℕ→Cover→ℝ:=fun _ _=>1; have hx:=fad hn (oneP hp') hs h H (Pose.epic_m (Pose.epic_m hf.fence hg.fence) hp.fence)
   erw [zero_add,show Oct R (f*g*p) T=(fun i=>∑ x∈pod (R i), f x*g x*p x) from funext fun i=>by simp only [T,Oct,Pi.mul_apply,mul_one]] at hx
   suffices he: eve U 0 k T=0 by
       change Fruit _ _ _ (fineI _ (_*eve U 0 k T)) at hx; rw [he,mul_zero] at hx; exact (by simpa only[fineI,Pi.zero_apply,mul_zero,integral_zero] using! hx)
   unfold eve; apply Finset.sum_eq_zero; intro i hi; suffices hx: slit U _ (stalkP i.toList T)=0 by rw [hx];simp
   have hp: i.toList ≠ []:=fun H=>by have he:i.toList.length=k:=(Multiset.length_toList _).trans ((cardA _).mp hi); rw [H] at he;simp only[List.length_nil] at he;omega
   rw [show stalkP i.toList T=(0:ℕ→Cover→ℝ) from ?_]; apply (tendsto_nhds_unique (nullC (k:=0+k) (U:=U) hp' |>.lo.slit.2.2)); simp only[Pi.zero_apply,mul_zero];exact tendsto_const_nhds
   obtain ⟨a,l,hh⟩:= List.exists_cons_of_ne_nil hp; rw [hh,←streak,show smear a T=0 from funext fun i=>funext fun x=>sub_self _]; exact funext fun i=> dvol_zero _
end permits
end YM.OPE.Nestle
