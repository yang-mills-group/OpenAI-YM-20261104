import YM.OPE.Compatible.Ash.Ether
/-!
# Down-shifted corona & Taylor
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{z:(i:ℕ)→Site (U.M i)}{D:List Axis}{k i m:ℕ}{f:Axis}{a:Cover}
lemma prune {s B r:ℝ}(hs:0<s)(hr:0<r)(hp: r ≤ ‖char (step f) (z i)-1‖) (hd: Drone U z) (he:U.h i*s ≤ 1)(hg:m=D.length+2+(k+1))
   (hh:‖char (step f) (z i)-1‖^m * ‖bandread (endband D a) s k z i‖ ≤ B*(U.h i*s)^k /(mesh (U.M i)/(U.h i*s))^4*(mesh (U.M i)/(U.h i*s))^m) : ‖glide U.q' k (fun i=>corona (U.h i) s D (z i+wrap _ a)) i‖ ≤ (U.h i)^k*(B/turn^4*(turn/r)^m)/s:=by
   let h:=U.h i; let T:=mesh (U.M i)/(U.h i*s); have hx: T=turn/s:=by unfold T; rw [U.mesh_h]; field_simp [(U.h_pos i).ne']
   rw [tide (hg:=trim_end D a) hd k i hs he _ (fun i=> corona_curry i hs)]
   apply (fieldConvert (c:=bandread (endband D a) s k z i) (v:=m) hs hr hx hg (le_trans _ hh) rfl).trans (le_of_eq (by rw [mul_pow, pow_succ s]; field_simp))
   gcongr
lemma glide_core {s:ℝ}(hs:0<s)(hv: Drone U z)(D:List Axis)(a:Cover)(k:ℕ):∃ C≥0,∀ᶠ i in atTop, ‖glide U.q' k (fun j=> piece (U.h j) s D (z j+wrap _ a)) i‖ ≤ C*(U.h i)^k:=by -- s binder
   obtain ⟨A,hA,he⟩:= band_low z hs a D k; let b:ℂ:=(s:ℂ)^((D.length:ℤ)-2); refine ⟨‖b‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩; filter_upwards [he,(U.h_null.mul_const s).eventually (ge_mem_nhds (show 0*s<1 from by simp))] with i hi hk
   rw [tide (g:=hotband D a) hv k i hs hk (fun u x hx=>trim_hot D a u x (le_trans one_le_two hx)) _ (b:=b) (fun j=> piece_curry j hs), norm_mul]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)
lemma Gloam.anti (U:Gloam):Antitone U.h:=by
    apply antitone_nat_of_succ_le; intro i; rw [U.h_succ]; apply div_le_self (U.h_pos _).le U.qsub.le
lemma macro_tax (hh: Drone U z)(hv:z 0≠0)(D:List Axis)(a:Cover)(k:ℕ)(hk: k>0):
    ∃ C≥0,∀ᶠ i in atTop, ‖glide U.q' k (fun j=> joint (U.h j) D (z j+wrap _ a)) i‖ ≤ C*U.h i^k:=by
   obtain ⟨f,R,hR,L⟩:=charCourt hh hv a; let m:=D.length+2+(k+1); let s:=turn*((m:ℝ)+1); have hs:0<s:=by dsimp only [s]; positivity
   obtain ⟨B,hB,oH⟩:=steel hR hk D; obtain ⟨C,hC,V⟩:= vet_bank U.qsub.le D a k m; let b:=C/turn^4*(turn/R)^m; obtain ⟨T,hT,HT⟩:= glide_core hs hh D a k; let A:=2*b/s+ T; obtain ⟨C',hC',H'⟩:=sterling (E:=ℂ) U.q' k; let E:=C'*(B*2^k); refine ⟨A+E,show 0≤A+E from by unfold A b E; positivity,?_⟩
   have hx : Tendsto (fun i=> mesh (U.M i)*m) atTop (𝓝 0):=by convert! ((U.h_null.const_mul turn).mul_const (m:ℝ)) using 1; simp
   obtain ⟨M,hM⟩:= eventually_atTop.mp ((hx.eventually (ge_mem_nhds (show (0:ℝ) < 1/2 from by norm_num))).and L); filter_upwards [HT,eventually_ge_atTop M,(U.h_null.mul_const s).eventually (ge_mem_nhds (show 0*s<1/2 from by simp))] with i Hi hi hs'
   let U₀(t:ℝ):ℕ→ℂ:=fun i=>piece (U.h i) t D (z i+wrap _ a); let u(t:ℝ):=glide U.q' k (U₀ t) i
   have hp:=U.h_pos i; obtain ⟨q,hq⟩:= threshold hs hp hs'; let Q(j:ℕ):=(2:ℝ)^j*s
   have hQs(j:ℕ):s ≤ Q j:=by unfold Q; grw [←one_le_pow₀ (show (1:ℝ)≤2 from by norm_num)]; simp
   have he(j:ℕ)(hj:j≤q): U.h i*Q j ≤ 1:=by unfold Q; rw [← mul_assoc]; grw [show (2:ℝ)^j ≤ 2^q from pow_le_pow_right₀ one_le_two hj]; exact hq.2
   have hV(j:ℕ)(hj:j<q): ‖u (2*Q j)-u (Q j)‖ ≤ U.h i^k*b/(2^j*s)^ (1:ℕ):=by
      have ht:= he j (le_of_lt hj); have hp':=lt_of_lt_of_le hs (hQs j); unfold u; rw [sub_eq_add_neg, ←glide_neg (U₀ (Q j)),←glide_add]; change ‖glide _ _ (U₀ (2*Q j) + -U₀ (Q j)) _‖≤_; rw [pow_one]
      rw [show (U₀ (2*Q j) + -U₀ (Q j))=(fun x:ℕ=>corona (U.h x) (Q j) D (z x+wrap _ a)) from funext (fun x=> (sub_eq_add_neg ..).symm)]
      have hm:= (hM i hi); refine prune (f:=f) (m:=m) hp' hR hm.2.2 hh ht rfl (V (U.M i) _ (mul_pos hp hp') ht hm.1 ?_ f (z i)); rw [U.mesh_h, mul_comm turn,mul_assoc]; exact mul_le_mul_of_nonneg_left (hQs j) hp.le
   let S:= Q q
   have hy:=peel hs u zero_lt_one (mul_nonneg (pow_nonneg hp.le _) (show 0≤b from by unfold b; positivity)) hV
   let F(i:ℕ):=outsideP (U.h i) S D (z i+wrap _ a)
   have T1: ‖u S‖ ≤ A*U.h i^k :=by
       have hα:= norm_add_le (u S-u s) (u s); rw [sub_add_cancel] at hα; apply (hα.trans (add_le_add hy Hi)).trans; have hα':0 ≤ U.h i^k*b/s:=by unfold b; positivity
       unfold A; rw [pow_one]; change 2*(1-(1/2:ℝ)^q)*(U.h i^k*b/s)+_≤_
       calc _ ≤ 2*(U.h i^k*b/s)+T*U.h i^k := by nlinarith only [hα', show 0≤(1/2:ℝ)^q from by positivity]
            _=_:=by ring
   have T2: ‖glide U.q' k F i‖≤ E*U.h i^k:=by
       have hh(j:ℕ):‖F (i+j)‖≤(B*2^k)*U.h i^k:=by
          have ho: M ≤ i+j:=by omega
          let r':=U.h (i+j); have hX:=mesh_pos (n:=U.M (i+j)); have hQs':=lt_of_lt_of_le hs (hQs q)
          have hm:=hM _ ho; have hv1:turn * (((D.length+2+k:ℕ):ℝ)+1) ≤ s:=by unfold s; gcongr; dsimp only [m]; omega
          apply (oH _ S hQs' (hv1.trans (hQs q)) ?_ ?_ f (z _+wrap _ a) hm.2.1).trans
          · have hE: 1 ≤ 2*S*U.h i:= by have hx:1/2 ≤ U.h i*S:= by simpa only[S,Q,mul_assoc] using! hq.1
                                        linarith only [hx]
            rw [div_le_iff₀ (pow_pos hQs' k)]
            calc _ ≤ B*((2*S*U.h i)^k) := le_mul_of_one_le_right hB (one_le_pow₀ hE)
                 _=_:=by unfold S; simp only [mul_pow];ring
          · apply le_trans _ (he q le_rfl); exact mul_le_mul_of_nonneg_right (U.anti (show i≤ i+j by omega)) hQs'.le
          apply le_trans _ hm.1; gcongr; unfold m; omega
       exact ((H' F i _ (fun j _=> hh j)).trans (le_of_eq (by unfold E;ring)))
   rw [show (fun i=>joint (U.h i) D (z i+wrap _ a))=U₀ S+F from funext (fun i=>clear_joint _ S ..), glide_add]; grw [norm_add_le, T2]; exact (add_le_add T1 (le_refl _)).trans (le_of_eq (by ring))
end YM.OPE.Balsam
