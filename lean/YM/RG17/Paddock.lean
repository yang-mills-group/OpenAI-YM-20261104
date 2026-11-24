import YM.RG17.Argon
/-!
# centers chosen near wheel (polynomial β motion), all requests on interval sparse geometry. For Agenda and trace samples.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec Table OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson Extraction Cells
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {s:Extraction.Sequence} (Z:Ledger L)(fx:Flick R.family.path.levels)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "O"=> OPE.run
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "K"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "t"=> (fun r=> H (K r))
local notation "o"=> (fun r=> r*t r)
include Z fx
lemma goingWheel : Height R.family.S home O K 1:=⟨(opt C fx Z.simple).1,(opt C fx Z.simple).2⟩
lemma runMount : RateIs home O t 0:=crestArmour (opt C fx Z.simple)

-- agenda, just enough for all b eventually on conf shapes. aX ≤ pcap
structure Lookup (m:ℝ→ℕ):Prop where
   spine : Height R.family.S home O m 1
   log : ∀ᶠ r in home,(r*H (wheel R.family r) ≤ R.family.S.a (m r+1) ∧ R.family.S.a (m r) ≤ r*H (wheel R.family r)^3) ∧ m r+1 < wheel R.family r
local notation "T'"=> Lookup R
lemma leasable : ∃ m:ℝ→ℕ, Lookup R m:=by
   have hu:RateIs home O o (-1):= ((show RateIs home O id (-1) from loglife (r:=id) (show home ≤ home from le_rfl)).mul (runMount R Z fx)).swap (by ring)
   let P:= R.family.S; let τ (r):=r*H (K r)
   let m (r:ℝ):= if h:0<τ r then Nat.find (show ∃ i,a (i+1)<τ r from ((R.family.S.shrinks.comp (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds h)).exists) else 0
   have he:∀ᶠ r in home, a (m r+1)< τ r ∧ (∀ i < m r,τ r ≤ a (i+1)):=by
       filter_upwards [hu.pos] with r hr; rw [show m r= _ from dif_pos (show 0< τ r from hr)]; exact ⟨Nat.find_spec (p:=fun i=>a (i+1)<τ r) _,fun i hi=> le_of_not_gt (Nat.find_min _ hi)⟩
   have hh:Tendsto m home atTop:=by
       refine tendsto_atTop.mpr fun i=>?_ ; filter_upwards [he,(hu.tends (by norm_num) ageLarge).eventually (gt_mem_nhds (R.family.S.a_pos (i+1)))] with r hr hv
       exact Nat.le_of_lt (Nat.lt_of_succ_lt_succ (R.family.S.strictAnti.lt_iff_gt.mp (hr.1.trans hv)))
   let l (r):= m r-1; have hl:Tendsto l home atTop:= tendsto_atTop.mpr fun i=> by filter_upwards [hh.eventually_gt_atTop i] with r hr; unfold l; omega
   have hW:∀ᶠ r in home,(τ r ≤ a (l r+1) ∧ a (l r) ≤ r*t r^3) ∧ l r+1 < K r:=by
       filter_upwards [positiveLength, he,hh.eventually_ge_atTop 1] with r hr he hh
       have hz: l r+1=m r:= Nat.sub_add_cancel hh; have hf:=he.2 (l r) (by omega); have ht:1<H (K r):= R.family.path.levels.fits.delayed _
       have hj: l r+1<K r:=by
          apply R.family.S.strictAnti.lt_iff_gt.mp; refine (lt_of_le_of_lt (le_mul_of_one_le_right (R.family.S.a_pos _).le (one_le_pow₀ ht.le)) ((spoke C hr).trans_lt (lt_mul_of_one_lt_right hr ht))).trans_le hf
       refine ⟨⟨hf,?_⟩,hj⟩ -- syntax
       let B':= R.family.S.block; have hp (i)(hu:i+1 ≤ K r) : a i ≤ a (i+1)*H (K r):=by
           let Y:ℝ:=(R.family.S.block i).val; have hz:Y ≠ 0:= by unfold Y; positivity
           have hx : Y ≤ H (K r):= (fx.grade i).trans ((by linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans ((C).path.levels.fits.delayed i))] : Real.log (H i) ≤ H i).trans (WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos Z.simple).le (by omega)))
           exact (show a i=a (i+1)*Y from by unfold Y at *; rw [R.family.S.a_step,div_mul_cancel₀ _ hz]).trans_le (mul_le_mul_of_nonneg_left hx (R.family.S.a_pos _).le)
       refine (hp (l r) hj.le).trans ?_; rw [hz]; refine (mul_le_mul_of_nonneg_right ((hp (m r) (by omega)).trans (mul_le_mul_of_nonneg_right he.1.le (zero_le_one.trans ht.le))) (zero_le_one.trans ht.le)).trans_eq (by unfold τ; ring)
   refine ⟨l,⟨hl,?_⟩,hW⟩
   have hV: RateIs home O (fun r=>a (l r)) (-1):=by
       exact RateIs.of_sandwich hu ((((show RateIs home O id (-1) from loglife (r:=id) (show home ≤ home from le_rfl)).mul ((runMount R Z fx).power 3)).swap (by norm_num)).pays ageLarge) (hW.mono fun i hi=>hi.1.1.trans (R.family.S.strictAnti.antitone (Nat.le_succ _))) (hW.mono fun i hi=>hi.1.2) ageLarge
   exact (show Tendsto (fun r=> -Real.log (a (l r))/O r) home (𝓝 1) from by simpa only [neg_div,neg_neg] using! hV.rate.neg).congr (fun r=>by rw [← Real.log_inv]; rfl)
variable {n:ℕ} (Y m:ℝ→ℕ) {x:Points n} {u:Filter ℝ} (b:ℝ→ Fin n→ Cover)
lemma mintages (h:Lookup R m) (hi:u≤home) (hk:∀ᶠ r in home,Y r ≤ m r)(ht:Tendsto (fun r=>tag (role R.family r) (b r)) u (𝓝 x))(hx:x∈generic n) : ∀ᶠ r in u, Plot R.family (Y r) (m r) (K r) (b r):=by
   let v (i: Fin n)(r:ℝ):=tag (role R.family r) (b r) i
   have he (i:Fin n): Tendsto (v i) u (𝓝 (x i)):= (show Continuous (fun x: Points n=> x i) from by fun_prop).continuousAt.tendsto.comp ht
   have hh0:Tendsto t u atTop:= ((Next.Rank.Station.hat_rate _ Z.simple).comp (turnsWheel C)).mono_left hi
   have hV(i:Fin n): ∀ᶠ r in u, 8*‖v i r‖<t r:=(by obtain ⟨c,hc⟩:=exists_gt (8*‖x i‖); filter_upwards [((he i).norm.const_mul 8).eventually (gt_mem_nhds hc),hh0.eventually_ge_atTop c] with r h he; exact h.trans_le he) -- name
   let Y'(r):ℝ:= (R.family.path.levels.budget (K r)).B
   have hP : ∀ᶠ r in u,∀ i j:Fin n,i≠j → 2*(role R.family r * Y' r^2)< ‖v i r-v j r‖:=by
       refine eventually_all.mpr (fun i=> eventually_all.mpr (fun j=>?_))
       by_cases hq:i=j; exact Eventually.of_forall fun _ h=>(h hq).elim
       have hx': 2*(0:ℝ)<‖x i-x j‖:=by simpa only [mul_zero] using norm_sub_pos_iff.mpr ((generic_conf _ hx).ne hq)
       obtain ⟨p,hp,hQ⟩:= exists_between hx'; filter_upwards [((bendsPrice Z fx).mono_left hi|>.const_mul 2).eventually (gt_mem_nhds hp), (((he i).sub (he j)).norm).eventually (lt_mem_nhds hQ)] with i hi hp _; exact hi.trans hp
   filter_upwards [positiveLength.filter_mono hi,h.log.filter_mono hi,hk.filter_mono hi,eventually_all.mpr hV,hP] with r hr hV hk hz hP
   have he' (i: Fin n): R.family.S.gridPoint (wheel C r) (b r i) = r • v i r:=congr_arg (fun x:Points n=> x i) (scaledRole («C»:=R.family) hr (b r)).symm
   refine ⟨fun i=>?_,fun i j e=>?_,hk,hV.2.le⟩
   · rw [he',norm_smul,Real.norm_of_nonneg hr.le,mul_left_comm]; exact (mul_lt_mul_of_pos_left (hz i) hr).trans_le hV.1.1
   dsimp only [Function.comp_apply]; rw [he',he', ← smul_sub,norm_smul,Real.norm_of_nonneg hr.le]; exact (show (2*a _)*_=r*(2*(role C r*Y' r^2)) from by unfold role Y'; field_simp).trans_lt (mul_lt_mul_of_pos_left (hP i j e) hr) -- multiplication assoc
end YM.RG17
