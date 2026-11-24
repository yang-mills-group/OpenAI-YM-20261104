import YM.OPE.Compatible.Ash.Fib
/-! # Arbitrary-order upper cap -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{z:(i:ℕ)→Site (U.M i)}{s:ℝ}{n:Side}
lemma mesh_tick (n:Side): mesh n=turn*dew n:=by unfold dew mesh; rw [div_eq_mul_inv]
lemma refD (f:Axis)(hh:Drone U z)(i:ℕ): char (step f) (z i)=char (step f) (z 0):=by
    induction i with
    | zero=>rfl
    | succ i ih=> rw [hh i,←ih,Pert.Full.swap]; simp only [show char ((U.ratio i).embed (z i)) (step f)=char (z i) (step f) by simpa only [wrap_step] using embed_sig (U.ratio i) (z i) (step f:Cover), Pert.Full.swap (z i)]
lemma existsF (p:Site n)(hp:p≠0):∃ f:Axis,0<‖char (step f) p-1‖:=by
   by_contra! he; apply hp; ext i
   have hx: char (step i) p=1:=sub_eq_zero.mp (norm_le_zero_iff.mp (he i)); rw [Pert.Full.swap] at hx; unfold char at hx; rw [← (ZMod.stdAddChar (N:=n.val)).map_zero_eq_one] at hx; apply ZMod.injective_stdAddChar at hx; rw [dot,Finset.sum_eq_single i] at hx; simpa only [step_apply,↓reduceIte,mul_one,Pi.zero_apply] using hx
   · simp only [step_apply]; intro _ _ hh; rw [if_neg hh,mul_zero]
   simp
lemma charCourt (hh:Drone U z)(hv:z 0≠0)(a:Cover):∃ f:Axis,∃ R>0,∀ᶠ i in atTop,R ≤ ‖char (step f) (z i+wrap _ a)-1‖ ∧ R ≤ ‖char (step f) (z i)-1‖:=by
   obtain ⟨f,hf⟩:=existsF _ hv
   let A:=char (step f) (z 0)
   have hx: Tendsto (fun i=> char (step f : Site (U.M i)) (wrap (U.M i) a)) atTop (𝓝 1):=by
      simp_rw [char_wrapped]; refine Filter.Tendsto.congr' (f₁:=fun i:ℕ=> Complex.exp ((corner a (mesh (U.M i) • basis f):ℝ)*Complex.I)) ?_ (?hw) -- eventual lift step = step
      swap; refine (show Tendsto (fun i:ℕ=> Complex.exp ((corner a (mesh (U.M i) • basis f):ℝ)*Complex.I)) atTop (𝓝 _) from ?_)
      · have ht: Tendsto (fun i=>mesh (U.M i)) atTop (𝓝 0):=by simpa only [U.mesh_h, mul_zero] using! (U.h_null.const_mul turn) -- simp
        have ho: Continuous (fun y:ℝ=>Complex.exp ((corner a (y • basis f):ℝ)*Complex.I)):=by unfold Pert.Full.corner; fun_prop
        convert! ho.continuousAt.tendsto.comp ht using 1; simp [corner]
      filter_upwards [U.sides.eventually (eventually_gt_atTop 2)] with i hi
      rw [moment, show Lattice.lift (step f: Site (U.M i))=step f by rw [lift_eq_iff]; refine ⟨(by exact (wrap_step ..).symm),fun j=>?_⟩; simp only [step_apply]; split <;> omega, incVec_step]
   have hw := (tendsto_const_nhds (x:=A)).mul hx
   have hD : Tendsto (fun i=>‖char (step f) (z i+wrap _ a)-1‖) atTop (𝓝 ‖A-1‖):=by
       simp_rw [char_add,refD _ hh]; convert! (hw.sub_const 1).norm using 1; rw [mul_one]
   refine ⟨f,‖A-1‖/2, half_pos hf,?_⟩; filter_upwards [hD.eventually (le_mem_nhds (half_lt_self hf))] with i hi; exact ⟨hi,by rw [refD _ hh]; exact (half_lt_self hf).le⟩
lemma fieldConvert {D:List Axis}{B r T:ℝ}{c b:ℂ}{v k:ℕ}(hs:0<s)(hh:0<r)(he:T=turn / s)(hk:v=D.length+2+k)
    (hg:r^v*‖c‖ ≤ B/T^4*T^v)(hc:b=(s:ℂ)^((D.length:ℤ)-2)*c):
    ‖b‖ ≤ (B/(turn^4)*(turn/r)^v) /s^k:=by -- remove w i
   rw [hc,norm_mul, show ‖(s:ℂ)^((D.length:ℤ)-2)‖=s^((D.length:ℤ)-2) from by exact_mod_cast Real.norm_of_nonneg (zpow_pos hs _).le]
   apply (mul_le_mul_of_nonneg_left ((le_div_iff₀ (pow_pos hh v)).mpr (mul_comm ‖c‖ _ ▸ hg)) (zpow_pos hs _).le).trans; apply le_of_eq; rw [he,zpow_sub₀ hs.ne', zpow_natCast,show s^(2:ℤ)=s^2 from by norm_cast,hk]; simp only [pow_add,div_pow]; field_simp
lemma roof_priced (r:ℝ)(hh:0<r)(D:List Axis)(k:ℕ):
 let m:=D.length+2+k
 ∃ B≥0,∀ (n:Side)(s:ℝ),0<s→ turn*((m:ℝ)+1)≤s → dew n*s≤1→ mesh n*m≤1/2 →∀ (i:Axis)(z:Site n),r≤‖char (step i) z-1‖→
   ‖corona (dew n) s D z‖ ≤ B/s^k ∧(1/2 ≤ dew n*s→ ‖outsideP (dew n) s D z‖≤ B/s^k):=by
   intro m; obtain ⟨C,hC,L⟩:= ctrl D m; refine ⟨C/(turn^4)*(turn/r)^m,by positivity,fun n s hs ht hw hm i z h =>?_⟩
   let H:=dew n; have hp:=dew_pos n; let t:ℝ:= H*s -- sed
   have hz: mesh n*(m+1) ≤ t:=by rw [mesh_tick, mul_comm turn,mul_assoc]; exact mul_le_mul_of_nonneg_left ht hp.le
   let T:= mesh n/t; have ht':T=turn/s:=by dsimp only [T,t,H]; rw [mesh_tick]; field_simp
   have he:= L (mul_pos hp hs) hw hm hz i z
   have hu: (n.val:ℂ)*(H:ℂ)=1:=by exact_mod_cast (mul_inv_cancel₀ (ne_of_gt (val_pos _)))
   constructor
   · apply fieldConvert (D:=D) (v:=m) (B:=C) hs hh ht' rfl (le_trans _ he.1) (by rw [corona_expand _ _ hp hs, show (n.val:ℂ)*(dew n:ℂ)=_ from hu, inv_one,one_pow,one_mul]); gcongr
   intro h'
   apply fieldConvert (D:=D) (v:=m) (B:=C) hs hh ht' rfl (le_trans _ (he.2 h')) (by rw [outside_expand _ _ hp hs, show (n.val:ℂ)*(dew n:ℂ)=_ from hu, inv_one,one_pow,one_mul]); gcongr
end YM.OPE.Balsam
