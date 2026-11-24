import YM.AllOrder.Quay.Kit
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Quay
open Function Filter Work Tensor Lattice Wilson RG Ovens Finset
open WilsonStartup WilsonStartup.Design WilsonStartup.Start WilsonStartup.Padded Floe Floe.Crest Till Tilt Burn
open PhysicalNext Repeat Pressure ConnectedActivityE6 ConnectedActivityE6.Coat Rosary
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {κ j k a c : ℕ}{σ ω' α T C:ℝ}
variable (p:BudgetPoint)(h:Clip)(β:ℝ)
-- Mask extension cost on Lens. again purchases in ONE merger. keep error+M physically true.
variable (k)
open AnalyticBridge VerifiedReset -- ambient naming.Not export.
local notation "B"=>p.B
local notation "sM"=> offerS G p (tile h G) (Age.scope (k+2)) (gStep β)
local notation "sH"=> pulpit h β G k n
local notation "w"=>Start.weight h β
local notation "t"=> p.threshold
local notation "I"=> Key n
variable (x:Site n)(U:Config G n)(i:Key n)
local notation "F"=> Key.accrual
abbrev shore (p:BudgetPoint)(i:WilsonStartup.Key n):=court i.native p.B
local notation "Y"=> shore (n:=n) p
abbrev rent (p:BudgetPoint)(h:Clip)(β:ℝ)(i:WilsonStartup.Key n) (U:Config G n):ℝ:= Start.weight h β*(masked p.threshold (court i.native p.B) i.accrual U - masked p.threshold i.skin i.accrual U)
def rush : Rosary.Cane G n (Key n):= ⟨Y,fun _=> ⟨_,halo_subset _ _ (mem_singleton_self _)⟩, rent p h β⟩
local notation "K"=> Quay.rush (G:=G) (n:=n) p h β
lemma flora : Cane.wiggles (h:=K):=by
 intro s b; refine ⟨Key.perm s b,fun i=> ⟨?_,?_⟩⟩
 · let e:= Push.Local.turnSites s b; change halo B {e i.native}= _; rw [←Finset.image_singleton]; exact Push.Local.halo_map e (Push.Local.turn_sep s b) ..
 let v:Seat n:=(s,b); let E:= Y i; have he: Y (Key.perm s b i)= v.spread E:= by let e:=Push.Local.turnSites s b; change halo B {e i.native}= _; rw [←Finset.image_singleton]; exact Push.Local.halo_map e (Push.Local.turn_sep s b) ..
 have hp: (Key.accrual (Key.perm s b i) (G:=G))= F i ∘ v.view:=funext fun i'=>congr_arg (residual G i.root) (Key.oriented i s b i');
 funext U; dsimp only [Function.comp_apply]; change rent _ _ _ _ _=rent _ _ _ _ _; unfold rent; unfold shore at he; rw [he,show (Key.perm s b i).skin=v.spread i.skin from Key.spun ..,hp,v.distribute,v.distribute]; rfl
section
variable (ht:2≤p.B)
local notation "E!"=> rent p h β i
include ht
lemma flash (he : Healthy t (Y i) U): (E!) U=0:= by unfold Quay.rent; rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (he.mono_left (sits p i ht)),sub_self,mul_zero]
lemma aware : GaugeInvariant (rent p h β i (G:=G)) ∧ UsesFinal t (Y i) (rent p h β i (G:=G)) ∧ Measurable (rent p h β i (G:=G)) ∧ ∀ U: Config G n,(E!) U≠0→ ¬Healthy t (Y i) U:= by
 let he:= accrual_regular (b:=p) (G:=G) i; let hX:= CouplingShape.reg_extend he (sits p i ht); exact ⟨fun k U=> congr_arg (w * ·) (congr_arg₂ (· - ·) (CouplingShape.stencil_gi he.symmetry t _ k U) (CouplingShape.stencil_gi he.symmetry t _ k U)),fun U V ha hf=>congr_arg (w * ·) (congr_arg₂ (·-·) (CouplingShape.stencil_reads _ hX.sites t U V ha hf) (Work.H03.reads_larger (sits p i ht) (CouplingShape.stencil_reads _ he.sites t) U V ha hf)), measurable_const.mul ((masked_measurable _ _ _ he.borel).sub (masked_measurable _ _ _ he.borel)), fun U hh hZ=> hh (flash p h β U i ht hZ)⟩ -- actual arguments inference from goal & ... ???
lemma crowd (v:ℝ)(hv:0≤v): Ac.Hit (Y) p.B (fun _=>v) (p.supportExponent+1) (costFace (((p.B+p.B+1:ℕ):ℝ)^4*(v*Real.exp (p.supportExponent+1)))):= by
 intro x; let g (x':Site n):= if x ∈ court x' p.B then v*Real.exp ((p.supportExponent+1)*coverNumber p.B (court x' p.B)) else 0; let d:=v*Real.exp (p.supportExponent+1); let V:Support n:=court x p.B; let L:= V.card; have hL:L≤(p.B+p.B+1)^4:= le_of_le_of_eq (Corona.halo_size ({x}:Support n) p.B) (by simp);
 have he y:y∈V ↔ x∈court y B:= by unfold V court; simp only [halo_spec, mem_singleton,exists_eq_left,separation_comm y]
 have hV(y:Site n):0≤g y∧g y ≤ if y∈V then d else 0:=by unfold g; simp only [he y]; split; refine ⟨mul_nonneg hv (Real.exp_pos _).le,?_⟩; unfold d; apply mul_le_mul_of_nonneg_left _ hv; exact Real.exp_monotone (mul_le_of_le_one_right (add_nonneg p.exponent_pos.le zero_le_one) (by exact_mod_cast Burn.shell p y)); exact ⟨le_refl _,le_refl _⟩
 refine ⟨fun i=> (hV i.native).1,Summable.of_finite,?_⟩; rw [tsum_fintype];
 have hh (f: Site n→ℝ) : (∑ i : Key n, f i.native)=costFace (∑ i:Site n,f i):= by rw [Fintype.sum_prod_type]; simp only [Key.native,Fintype.sum_prod_type (f:=fun x' : WilsonStartup.Cell n=> f x'.1),Finset.sum_const,nsmul_eq_mul,←mul_sum,costFace,card_univ,mul_assoc]
 change (∑ i:Key n,g i.native) ≤ _; rw [hh]; unfold costFace; have hd:0≤d:=mul_nonneg hv (Real.exp_pos _).le; apply mul_le_mul_of_nonneg_left _ (by positivity); refine le_trans (Finset.sum_le_sum (fun i _=>(hV i).2)) ?_; rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]; simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL) hd
local notation "D"=>item G p
abbrev wad (v:ℝ):ℝ:=costFace (((p.B+p.B+1:ℕ):ℝ)^4*(v*Real.exp (p.supportExponent+1)))
local notation "a!"=> |Start.weight h β| *D
lemma todays (he:p.threshold ≤ Start.threshold G p.order p.power): (K).Ready p (wad p (|Start.weight h β| *item G p)):= by
 have h0:D≥0:= (item_pos G p).le; have hh: 0≤ a! := mul_nonneg (abs_nonneg _) h0;
 refine ⟨flora p h β,fun i=>aware p h β i ht,fun _=> a!, fun i U=> ?_, crowd (n:=n) p ht _ hh⟩
 change ‖rent p h β i U‖≤_; by_cases hQ : Healthy t (Y i) U; · rw [flash p h β U i ht hQ,norm_zero]; exact hh
 by_cases hy: Healthy t i.skin U; swap; · unfold rent; rw [masked_ne _ _ _ _ hQ, masked_ne _ _ _ _ hy]; simpa using hh
 unfold rent; rw [masked_ne _ _ _ _ hQ,masked_eq _ _ _ _ hy,zero_sub,norm_mul,norm_neg]; exact mul_le_mul_of_nonneg_left ((accrual_fit (b:=p) (G:=G) i he).2 U hy [] (by simp) (by simp)) (norm_nonneg _)
end
section
-- analytic Early equation opportunity
variable (hk:4*(k+4)≤ p.B)(hb:0<β)
include hk hb
lemma site_voice : (∑ i:Site n, (masked p.threshold (court i p.B) (sH i) U + masked p.threshold (court i p.B) (sM n i) U))=(raw G n h p β).additive p U + ∑' i, (K).values i U:= by
 let f(i : Key n):= masked p.threshold (Y i) (F i) U; have hu(x:Site n):masked p.threshold (court x p.B) (sH x) U+masked p.threshold (court x p.B) (sM n x) U=w*∑ s:Signed, ∑ j:PlaqAxes, f (batch x s j):= by
    by_cases he:Healthy p.threshold (court x p.B) U
    · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ he,add_comm, stageW k p h β x U hk hb]; unfold f orbit; simp only [Finset.sum_apply]; simp only [batch,shore,Key.native,he,masked_eq]; -- syntax? simp_rw requires proof applied.
    rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he]; have hψ (s:Signed)(q:PlaqAxes):f (batch x s q)=0:= masked_ne _ _ _ _ he; simp only [hψ, add_zero,Finset.sum_const_zero,mul_zero]
 rw [written_sum,tsum_fintype]; dsimp only [Quay.rush,Quay.rent]; simp only [← mul_sum,Finset.sum_sub_distrib]; rw [show ∑ x:Site n, _ = _ from Finset.sum_congr (f:=fun x:Site n=> masked p.threshold (court x p.B) (sH x) U+masked p.threshold (court x p.B) (sM n x) U) rfl (fun i _=> hu i)]; rw [←mul_sum,mul_sub_left_distrib,add_comm (_ *_),sub_add_cancel]; apply congr_arg; rw [Finset.sum_comm,Fintype.sum_prod_type]; exact Finset.sum_congr rfl (fun i _=> (Fintype.sum_prod_type (fun j:WilsonStartup.Cell n=>f (i,j))).symm)
end
end YM.AllOrder.Quay
