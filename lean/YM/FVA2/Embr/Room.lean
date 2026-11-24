import YM.FVA2.Embr.Vert
/-!
 # Room bounds on a shared tag aperture
 Costs here **after** entire epoch/plot/order fixed. Prove comparability of Fk's
 chord-prices to the climate paid potential on this inversion history.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Hearth.Clan RGComparison.Core16 Lumen Fk Forge
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {c f n:Side} {L:Fabric G n} (T:Cloth L)(w:L.Accounts→ℝ→ℝ)

-- chart calculus
lemma maximum_price {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{f:E→ℝ}(p:Stationary f) : ∃ C>0, ∀ᶠ u:E in 𝓝 0, f u ≤ C*‖u‖^2:= by
 let D:= iteratedFDeriv ℝ 2 f 0; let k:ℝ:=(Nat.factorial 2:ℝ)⁻¹
 have Hv (u:E): jet f 2 u≤ k*‖D‖*‖u‖^2:= by
    refine (Real.le_norm_self _).trans ?_; unfold jet; rw [norm_mul]; change ‖k‖ * _ ≤ _; have hk : 0≤k:= by unfold k; positivity
    simpa only [Real.norm_of_nonneg hk,mul_assoc k,prod_const,card_univ,Fintype.card_fin] using mul_le_mul_of_nonneg_left (D.le_opNorm (fun _=>u)) hk
 obtain ⟨a,C,hA,hC,H⟩:= p.dominated (c:=1) zero_lt_one
 refine ⟨ k*‖D‖+1, by unfold k; positivity,?_⟩; filter_upwards [closedBall_mem_nhds (0:E) hA] with u hu
 have hp:= (H u 1 one_pos (by rw [one_mul]; exact mem_closedBall_zero_iff.mp hu)).2; rw [Radial.higher,one_smul,one_pow,div_one,one_mul,Real.norm_eq_abs, abs_le] at hp; nlinarith [hp.1,Hv u]

section
variable (G)
open Asymptotics
lemma usage : ∃ A>0,∀ᶠ x:G.El in 𝓝 1,‖G.plog (G.mat x)‖ ≤ A * G.chord x:= by
 have hg:=G.colorScale_pos; obtain ⟨C,hC,H⟩:= G.plog_diff.differentiableAt (by simp) |>.hasFDerivAt.isBigO_sub.exists_pos
 have hv:Tendsto G.mat (𝓝 1) (𝓝 1):= G.continuous_mat.tendsto _
 refine ⟨C*G.colorScale,by positivity,?_⟩; filter_upwards [hv.eventually H.bound] with x hx; unfold Gauge.chord; rw [G.plog_one,sub_zero] at hx; refine hx.trans_eq ?_; change _=_*( _/G.colorScale); field_simp
lemma mint : ∃ A>0,∀ᶠ x:G.Color in 𝓝 0, G.chord (G.lieExp x) ≤ A*‖x‖:= by
 have h:=G.colorScale_pos; obtain ⟨C,hC,H⟩:= G.expDiff_zero.isBigO_sub.exists_pos; refine ⟨C/G.colorScale,by positivity,?_⟩; filter_upwards [H.bound] with x hx; change (‖G.mat _ - (1:G.Mat)‖) / G.colorScale≤_; rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right h]; simp only [G.mat_lieExp_zero,G.mat_one,sub_zero] at hx; exact hx
end

-- use vector price; includes rank-zero empty Warm event (for trivial epoch)
abbrev temple := ℝ × Facade.Panel T
variable (y:Flats G (Bottom L))(t:Clan L)
abbrev desk (r:ℝ)(t:Clan L)(x:Warm T→G.El):= spends L (fun i=>w i r) (committed T y r x) t
def go (x:Warm T→G.El) : Facade.Panel T:= fun i=>G.plog (G.mat (x i))
lemma go_one : go T 1=0:= funext (fun i=>by change G.plog (G.mat 1)=0; simp)
lemma go_cont : Tendsto (go T) (𝓝 1) (𝓝 0):= tendsto_pi_nhds.mpr fun i=>
   ( G.plog_one ▸ G.plog_diff.continuousAt.tendsto : Tendsto G.plog (𝓝 1) (𝓝 0)).comp ((G.continuous_mat.comp (continuous_apply i)).tendsto (1:Warm T→ G.El))
lemma hallIn : ∀ᶠ x in 𝓝 ((0:ℝ),(1:Warm T→G.El)), expLinks G _ (go T x.2)=x.2:= by filter_upwards [eventually_all (ι:=Warm T)|>.mpr (fun i=> (( (continuous_apply i).comp continuous_snd).tendsto ((0:ℝ),(1:Warm T→G.El))).eventually G.plog_right) ] with x hx; exact funext hx
lemma hotlinks: Tendsto (Function.uncurry (committed T y)) (𝓝 ((0:ℝ),(1:Warm T→G.El))) (𝓝 1):= by
 have he: committed T y 0 1=1:=by rw [committed,zero_smul,Inherit.identity_zero, door_one]; exact rear_one L
 exact he ▸ (committed_cont T y).tendsto _
where
 rear_one {n:Side}(L:Fabric G n): rear L 1 1=1:=by cases L with
                                                        | endcap=> funext i; cases i; rfl; next i=> exact Empty.elim i
                                                        | layer S H t hf L=> funext i; cases i; rfl; exact congr_fun (rear_one L) _
 termination_by structural L
local notation "Y"=> Facade.raise (Facade.rate T) w y
local notation "D" => desk T w y

lemma greeting : ∀ᶠ x:ℝ ×(Warm T→G.El) in 𝓝 (0,1),∀ t:Clan L,Y (x.1,go T x.2)=x.1^2+D x.1 t x.2:= by filter_upwards [(hotlinks T y).eventually (impression L),hallIn T] with x h hx t; rw [truePrice,hx]; exact congr_arg (_+·) (h _ t).symm

variable {Y₀ : L.Accounts→PowerSeries ℝ}{p:ℕ} (h:∀ i,0<term (Y₀ i) 0)(hp:∀i,Through p (amount (w i)) (Y₀ i))(H:∀i,ContDiffAt ℝ ω (w i) 0)
include h hp H
local notation "U"=> ((0:ℝ),(1:Warm T→G.El))

lemma minimum_in : ∃ A>0,∀ᶠ x in 𝓝 U,∀ (t: Clan L)(i:Warm T), Forge.nib x.2 i ≤ A *(x.1^2+ D x.1 t x.2):= by
 obtain ⟨a,ha,F⟩:= Laplace.rem (Facade.steep T Y₀ h w y H p hp); obtain ⟨C,hC,Q⟩:= mint G
 let f (x:ℝ×(Warm T→G.El)) : temple T:= (x.1, go T x.2); have hv:Tendsto f (𝓝 U) (𝓝 0):= Tendsto.prodMk_nhds (continuous_fst.tendsto _) ((go_cont T).comp (continuous_snd.tendsto _))
 refine ⟨ C^2/a,by positivity,?_⟩; filter_upwards [greeting T w y,hv.eventually F, hallIn T,eventually_all.mpr fun i=> (hv.eventually (((continuous_apply i).comp continuous_snd).tendsto (0:temple T) |>.eventually Q)) ] with x hx hq hb hg t i
 rw [←hx t]; let s:= G.chord (x.2 i); suffices he:s ≤ C * ‖f x‖ by
    have hi:= pow_le_pow_left₀ (G.chord_nonneg _) he 2; rw [mul_pow] at hi; change s^2≤_; refine hi.trans ((mul_le_mul_of_nonneg_left ((le_div_iff₀ ha).mpr ((mul_comm _ a).trans_le hq)) (by positivity)).trans_eq (by change C^2*(Y (f x)/a)=_*Y (f x); ring))
 exact (show s ≤ C*‖(f x).2 i‖ from (congr_arg G.chord (congr_fun hb i)).symm.trans_le (hg i)).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm (f x).2 i).trans (le_max_right _ _)) hC.le)

lemma maximum_in : ∃ A>0,∀ᶠ x in 𝓝 U,∀ t:Clan L,D x.1 t x.2 ≤ A*(x.1^2+∑ i,nib x.2 i):= by
 obtain ⟨a,ha,F⟩:= maximum_price (Facade.steep T Y₀ h w y H p hp).toStationary; obtain ⟨C,hC,Q⟩:= usage G;
 let f (x:ℝ×(Warm T→G.El)) : temple T:= (x.1, go T x.2); have hv:Tendsto f (𝓝 U) (𝓝 0):= Tendsto.prodMk_nhds (continuous_fst.tendsto _) ((go_cont T).comp (continuous_snd.tendsto _))
 refine ⟨a*(C^2+1),by positivity,?_⟩; filter_upwards [greeting T w y,hv.eventually F,eventually_all.mpr fun i=> ((continuous_apply i).comp continuous_snd).tendsto ((0:ℝ),(1:Warm T→G.El)) |>.eventually Q] with ⟨v,x⟩ hx hq hg t
 let s:= ∑ i,nib x i; have hs:0≤ s:= sum_nonneg (fun _ _=> sq_nonneg _ ); let L0:=(C^2+1)*(v^2+s); have hL:0≤L0:= by unfold L0; positivity
 suffices H: ‖(v,go T x)‖^2 ≤ L0 by have hm := mul_le_mul_of_nonneg_left H ha.le; specialize hx t; change Y (v,go T x) =_ at hx; unfold f at hq; change D v t x ≤ a*(_+_)*(v^2+s); rw [mul_assoc]; exact (((le_add_of_nonneg_left (sq_nonneg v)).trans_eq hx.symm).trans hq).trans hm
 apply le_trans _ (Real.sq_sqrt hL).le; apply pow_le_pow_left₀ (by positivity) _; rw [Prod.norm_def, max_le_iff]; constructor
 · change ‖v‖≤ _; have he:‖v‖^2 ≤ L0:= by rw [Real.norm_eq_abs,sq_abs]; unfold L0; nlinarith only [hs,sq_nonneg C,sq_nonneg (C*v),mul_nonneg (sq_nonneg C) hs]
   exact Real.le_sqrt_of_sq_le he
 · change ‖go T x‖ ≤ _; rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]; intro i; have he:= pow_le_pow_left₀ (norm_nonneg _) (hg i) 2; change ‖(go T x) i‖^2 ≤ (_*G.chord (x i))^2 at he; rw [mul_pow] at he; refine Real.le_sqrt_of_sq_le (he.trans (mul_le_mul_of_nonneg_left (single_le_sum (f:=nib x) (fun i _=> sq_nonneg _) (mem_univ _)) (sq_nonneg _)|>.trans ?_)); change C^2*s ≤ _; unfold L0; nlinarith only [hs,sq_nonneg (C*v),sq_nonneg v]
end YM.FVA2.Embr
