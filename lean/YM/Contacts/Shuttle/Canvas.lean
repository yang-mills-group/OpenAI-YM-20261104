import YM.Contacts.Shuttle.Glacier
import YM.Extra.WILSON_STARTUP.Taylor
/-!
# Addresses with full pullback, real smooth test library

Infinite position tests; only finitely many local orders go into the repeated
deterministic Mark step estimate. Detector will use this bookkeeping to link
to the actual finite probes. Adapt local bound from WilsonStartup.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Shuttle.Pigment
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open MeasureTheory Metric Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Pulse.Spine Origin
open Milling Milling.Steam Milling.Forge Tensor MultiNext.SignedSource Pattern Tide Morning WilsonStartup -- remove
open scoped Classical Topology BigOperators NNReal Matrix ContDiff
variable {G:Gauge}{h d k r n u:ℕ}{X Y E:Type}{s t δ b c:ℝ}
-- Costs around UNIT BALL budget. Supports of top probes stay in this (can allow other before-stage radii, here enough). 
-- native shelf radius 4.
def Cards : Submodule ℝ (E4→ℝ) where
  carrier := {f|ContDiff ℝ ∞ f}
  zero_mem':= (show ContDiff ℝ ∞ (fun _:E4=>(0:ℝ)) from contDiff_const)
  add_mem' {f g} hf hg:= (show ContDiff ℝ ∞ f from hf).add hg
  smul_mem' a _ h:= (show ContDiff ℝ ∞ _ from h).const_smul a
lemma Cards.able (f: Cards)(k:ℕ): ContDiff ℝ k f.val:= (show ContDiff ℝ ∞ f.val from f.property).of_le (show (k:WithTop ℕ∞) ≤ ∞ by exact_mod_cast (show (k:ℕ∞)≤⊤ from le_top))
instance : CoeFun (↥Cards) (fun _=> E4→ℝ):= ⟨Subtype.val⟩
variable (D:ℕ)
def Costs (f:Cards)(b:ℝ) := ∀ i:ℕ,i≤ D → ∀ x:E4,‖x‖ ≤ 4 → ‖iteratedFDeriv ℝ i f.val x‖ ≤ b
namespace Cards
def onRoute (x:E4)(t:ℝ)(f: Cards): Cards:= ⟨fun z=> f (x + t • z),(show ContDiff ℝ ∞ f.val from f.property).comp (show ContDiff ℝ ∞ (fun z:E4=> x+t • z) from contDiff_const.add (contDiff_id.const_smul t))⟩
theorem reach (f:Cards): ∃ b:ℝ,0≤ b ∧ Costs D f b:= by
   let K:= closedBall (0:E4) 4; choose b hb using fun i:ℕ=> (isCompact_closedBall (0:E4) 4).bddAbove_image (((Cards.able f i).continuous_iteratedFDeriv (m:=i) le_rfl).norm.continuousOn);
   refine ⟨∑ i∈Finset.range (D+1),|b i|,sum_nonneg fun i _=> abs_nonneg _,fun i hi x hx=>?_ ⟩; exact (show _≤b i from hb i ⟨x,(by simpa using hx),rfl⟩).trans ((le_abs_self _).trans (single_le_sum (f:=fun i=> |b i|) (fun i _=> abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))))
def pure (v:T E4 ℝ k): Cards:= ⟨Tensor.diagonal v,show ContDiff ℝ ∞ _ from diag_smooth v _⟩
lemma rent (i n:ℕ):∃ b:ℝ,0≤b ∧ ∀ v:T E4 ℝ n, Costs i (pure v) (b*‖v‖):= by
   let T':=Tensor.T E4 ℝ n; let f (a:T'× E4):= Tensor.diagonal a.1 a.2; have hf : ContDiff ℝ ω f:= by
      let P(x:E4):= ContinuousMultilinearMap.apply ℝ (fun _ : Fin n=> E4) ℝ (fun _=>x); have hh: ContDiff ℝ ω P:= contDiff_clm_apply_iff.mpr fun v=> diag_smooth v _
      exact ((hh.comp contDiff_snd).clm_apply (g:=fun v:T'× E4=> v.1) contDiff_fst)
   choose b hb using fun i:ℕ=> ((isCompact_closedBall (0:T') 1).prod (isCompact_closedBall (0:E4) 4)).bddAbove_image (contDiff_partial (Function.curry f) hf i).continuous.norm.continuousOn
   let B:=∑ k∈Finset.range (i+1),|b k|; have hB:0≤B:= sum_nonneg fun i _=> abs_nonneg _; refine ⟨B,hB, fun v k hk x hx=>?_⟩; by_cases hy:v=0; · subst v; simp_rw [show (pure (0:T E4 ℝ n)).val=(fun _=> (0:ℝ)) from rfl]; simp
   let a:ℝ:=‖v‖; let y:= a⁻¹ • v; have ha:0<a:=norm_pos_iff.mpr hy; have hp : ‖y‖ = 1:= by unfold y; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact inv_mul_cancel₀ ha.ne'; -- use below
   have he:‖iteratedFDeriv ℝ k (pure y).val x‖ ≤ B:= (show _ ≤ b k from hb k ⟨(y,x),⟨by simp [hp],by simpa using hx⟩,rfl⟩).trans ((le_abs_self _).trans (single_le_sum (f:=fun i=> |b i|) (fun j _=> abs_nonneg _) (show k ∈ Finset.range (i+1) from Finset.mem_range.mpr (by omega))))
   rw [show (pure v).val=a • (pure y).val from ?_, iteratedFDeriv_const_smul_apply ((able (pure y) k).contDiffAt), norm_smul,Real.norm_of_nonneg ha.le]; exact (mul_le_mul_of_nonneg_left he ha.le).trans_eq (mul_comm ..); rw [show v=a • y from (smul_inv_smul₀ ha.ne' v).symm] -- causes rw everywhere? guard
   rfl
variable {D}
lemma opDown (f:Cards)(z x:E4)(i:ℕ)(hs:0≤ s) : ‖iteratedFDeriv ℝ i (onRoute z s f).val x‖ ≤ ‖iteratedFDeriv ℝ i f.val (z+s • x)‖*s^i:= by
   let p:E4→L[ℝ] E4 := s • (ContinuousLinearMap.id ℝ E4); let u(x):= f (z+x); have he : (onRoute z s f).val=u∘p:=rfl; rw [he,p.iteratedFDeriv_comp_right (show ContDiff ℝ i u from (able f i).comp (contDiff_const.add contDiff_id)) x (le_refl (i:WithTop ℕ∞))]; unfold u; rw [iteratedFDeriv_comp_add_left]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; simp [p]; gcongr; exact ContinuousLinearMap.opNorm_le_bound _ hs fun x=> by simp [norm_smul,Real.norm_of_nonneg hs]
lemma powCosts {f:Cards}(hg:Costs D f b)(z:E4)(hs:0≤ s)(hr:‖z‖+s*4 ≤ 4)(i:ℕ)(hi:i≤D)(x:E4)(hx:‖x‖ ≤ 4): ‖iteratedFDeriv ℝ i (onRoute z s f).val x‖ ≤ b*s^i:= by refine (opDown f _ _ i hs).trans (mul_le_mul_of_nonneg_right (hg _ hi _ ?_) (by positivity)); apply (norm_add_le ..).trans; rw [norm_smul,Real.norm_of_nonneg hs]; exact (add_le_add_right (mul_le_mul_of_nonneg_left hx hs) _).trans hr
private lemma roughness (f:Cards)(h: FlatAt k f.val 0)(hb:∀ x,‖x‖≤4→ ‖iteratedFDeriv ℝ k f.val x‖ ≤ c)(hc:0≤ c) :∀ j≤k,∀ x,‖x‖≤4→ ‖iteratedFDeriv ℝ j f.val x‖ ≤ c * ‖x‖^(k-j):= by
   intro j hj; induction hj using Nat.decreasingInduction with
   | self=> simpa using hb
   | of_succ l hl ih=>
     intro x hx; let J:=iteratedFDeriv ℝ l f.val; have hm (y:E4)(hy:y∈closedBall (0:E4) ‖x‖) : ‖fderiv ℝ J y‖ ≤ c* ‖x‖^(k-(l+1)):= calc
       _ = ‖iteratedFDeriv ℝ (l+1) f.val y‖:= by rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply, LinearIsometryEquiv.norm_map]
       _ ≤ c*‖y‖^(k-(l+1)):= ih y ((le_of_le_of_eq (by simpa using hy) rfl).trans hx)
       _ ≤ _:= by gcongr; simpa using hy
     have he := (convex_closedBall (0:E4) ‖x‖).norm_image_sub_le_of_norm_fderiv_le (fun y _=> (Cards.able f k).contDiffAt.differentiableAt_iteratedFDeriv (x:=y) (by exact_mod_cast hl)) hm (x:=0) (y:=x) (by simp) (by simp)
     rw [show k-l=k-(l+1)+1 by omega,pow_succ, ← mul_assoc]; simpa only [J,h l hl,sub_zero] using! he
open PertExtension.Series Radial Ion
private lemma priced {f:E4→ℝ} (hf:f∈Powers.space E4 ℝ k) : ∀ j>k, iteratedFDeriv ℝ j f 0=0:= by
   rw [← Tide.arrangement] at hf; obtain ⟨A,rfl⟩:=hf; let f (i:Fin (k+1)):= Tensor.diagonal (A i); have he i := (diag_smooth (A i) ω).contDiffAt (x:=0); change ∀ j>k,iteratedFDeriv ℝ j (∑ i,f i) 0=0; intro j hj; rw [iteratedFDeriv_sum_apply (fun i _=> (he i).of_le le_top)]; apply Finset.sum_eq_zero; intro i _; apply Tensor.ext_diag _ _ ((he i).iteratedFDeriv_comp_perm) (fun _ _=>rfl) (funext fun x=>?_); have hh: Radial.jet (f i) j x=0:= by rw [radiant (he i).analyticAt i.val j (fun x t=> Tensor.homogeneous _ x t) x,if_neg (by omega)]
   exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j))
def plant (i:ℕ)(f:Cards): Cards := pure (Tensor.coeff f.val i 0)
def moth (k:ℕ)(f:Cards) : Cards:= f-∑ i∈Finset.range (k+1),plant i f
lemma molted (k:ℕ)(f:Cards) : (moth k f).val= f.val- Work.G05.blockTaylor k f.val:= by unfold moth; simp [plant,pure,Work.G05.blockTaylor]
private lemma held (k:ℕ)(f:Cards) (x:E4)(hh:k < h): iteratedFDeriv ℝ h (Work.G05.blockTaylor k f.val) x=0:= by
   let A:=Work.G05.blockTaylor k f.val; have he:A∈ Powers.space E4 ℝ k:= (Powers.space ..).sum_mem (fun i (hi: i∈ Finset.range (k+1))=> Powers.residence (Tide.lit _) (Nat.le_of_lt_succ (mem_range.mp hi)))
   have hw:= priced (Trace.Quill.origin x A he) h hh; rwa [iteratedFDeriv_comp_add_right,zero_add] at hw
lemma meadow {f:Cards}(hf:Costs D f b)(z:E4)(hs:0≤ s)(hd:s≤1)(hc:0≤ b)(hx:‖z‖+s*4≤4)(hi:k+1 ≤D): Costs D (moth k (onRoute z s f)) (b*s^(k+1)*4^(k+1)) := by
   let F:= onRoute z s f; have he (j:ℕ)(hj:k<j)(x:E4): iteratedFDeriv ℝ j (moth k F).val x=iteratedFDeriv ℝ j F.val x:= by rw [molted,iteratedFDeriv_sub_apply ((able F j).contDiffAt) (Work.G05.blockTaylor_contDiff .. |>.contDiffAt), held k F x hj,sub_zero]
   have h':= flat_sub_taylor F.val k (Cards.able F k |>.contDiffAt); rw [←molted] at h'
   have hv := roughness (moth k F) h' (c:=b*s^(k+1)) (fun x hx' => by rw [he _ (Nat.lt_succ_self _)]; apply powCosts hf _ hs hx _ hi _ hx') (by positivity)
   intro j hj x hX; by_cases hk:j≤k+1
   · exact (hv j hk x hX).trans (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hX _).trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le ..))) (by positivity))
   rw [he j (by omega)]; apply (powCosts hf _ hs hx j hj _ hX).trans; refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs hd  (le_of_lt (Nat.lt_of_not_ge hk))) hc).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))) -- le?
lemma colored_plant (f: Cards)(i:ℕ): Powers.home (plant i f).val i:= Tide.lit _
lemma planted (i D:ℕ)(hi:i≤ D):∃ c≥(0:ℝ),∀ (f:Cards)(z:E4)(s b:ℝ), 0≤ s→ 0≤ b→ ‖z‖+s*4≤4 → Costs D f b→ Costs D (plant i (onRoute z s f)) (c*(b*s^i)):= by
   obtain ⟨c,hc,hQ⟩:= Cards.rent D i; let a:ℝ:=((i.factorial:ℝ)⁻¹); refine ⟨c*a,by unfold a; positivity,fun v z s b hs hb h hr=>?_⟩; let V:=Tensor.coeff (onRoute z s v).val i 0; have he: ‖V‖ = a*‖iteratedFDeriv ℝ i (onRoute z s v).val 0‖:=by unfold V Tensor.coeff a; rw [norm_smul,Real.norm_of_nonneg (by positivity)]
   intro j hj x hx; apply (hQ V _ hj x hx).trans; rw [he]; have hh:= powCosts hr z hs h i hi 0 (by simp); exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by unfold a; positivity)) hc).trans_eq (mul_assoc ..).symm
end Cards
end YM.Contacts.Shuttle.Pigment
