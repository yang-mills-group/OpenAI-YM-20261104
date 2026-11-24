import YM.XSpace.Quotient
/-!
# Locally discrete real singlet outputs in the orthogonal orbit

Use distance in operator norm (no smooth distance facts). Points realizing the
orbit equality not assumed a priori to follow even a continuous trajectory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sample
open Function Set Filter MeasureTheory Maxwell Maxwell.Free
open scoped BigOperators Topology Classical RealInnerProductSpace ContDiff
variable {G : Gauge} {X Y:Motor G} {d :ℕ} {p: WickPol G}
local notation "O" => (1:Motor G)
lemma Rot.one : Rot (1:Motor G):=fun _=>rfl
lemma Rot.multiply (h:Rot X) (he:Rot Y): Rot (X*Y):=fun x=>(h _).trans (he x)
lemma Rot.revert (h:Rot X): ∃ Y, Rot Y ∧ X*Y=1∧Y*X=1:=by
  let E:G.Color →ₗᵢ[ℝ] G.Color:=⟨X,h⟩
  let L:= LinearIsometryEquiv.ofSurjective E (LinearMap.surjective_of_injective (f:=X.toLinearMap) E.injective)
  exact ⟨L.symm.toLinearIsometry.toContinuousLinearMap, L.symm.norm_map, ContinuousLinearMap.ext L.apply_symm_apply,ContinuousLinearMap.ext L.symm_apply_apply⟩
lemma rot_set: IsCompact (setOf (Rot (G:=G))):=by
  have he : {X:Motor G| Rot X}= ⋂ x:G.Color,{X| ‖X x‖=‖x‖}:=by ext X; simp [Rot]
  refine (isCompact_closedBall (0:Motor G) 1).of_isClosed_subset (he ▸ isClosed_iInter (fun i=> isClosed_eq (f:=fun T:Motor G=> ‖T i‖) (by fun_prop) continuous_const)) ?_
  intro x hx; rw [Metric.mem_closedBall,dist_zero_right]; exact x.opNorm_le_bound zero_le_one (fun i=> ((hx i).le.trans (by simp)))

def tag (p:WickPol G) (M : Motor G) : TaylorTower G→ℂ:=fun T=> play p T M
def Crown (p:WickPol G) (f:TaylorTower G→ℂ):= setOf (Rot (G:=G)) ∩ {M|tag p M=f}
def nearest (p:WickPol G) (M : Motor G): Prop:=∀ x∈ Crown p (tag p M), ‖M-1‖ ≤ ‖x-O‖
lemma hugging {f} (h : (Crown p f).Nonempty):∃ x ∈ Crown p f, nearest p x:=by
  have hc : IsCompact (Crown p f):=rot_set.inter_right (show IsClosed {X|tag p X=f} from isClosed_eq (f:=tag p) (continuous_pi fun i=> (travel_smooth ..).continuous) continuous_const)
  obtain ⟨x,hx,he⟩:=hc.exists_isMinOn h (f:=fun x=> ‖x-O‖) (by apply Continuous.continuousOn; fun_prop)
  exact ⟨x,hx, fun i hh=> he (hx.2 ▸ hh)⟩

section contradiction
variable (Y : ℕ → Motor G) (F : Motor G) (g:G.Simple) (h : p∈shellSector G d) (hY :∀ i,Rot (Y i)) (H : ∀ i,Singlet (tag p (Y i))) (he : ∀ i, Y i≠1)

include hY in
lemma deviation (hh : Tendsto Y atTop (𝓝 1)) (hv : Tendsto (inspect Y 1) atTop (𝓝 F)): OrthoDev F:=by
  intro x; let f:Motor G→ ℝ:=fun M=> ‖M x‖^2
  let L:= ContinuousLinearMap.apply ℝ G.Color x
  have hs:= (hasStrictFDerivAt_norm_sq (L O)).hasFDerivAt.comp (1:Motor G) L.hasFDerivAt; have hf:= watches hh hv hs; dsimp only [Function.comp_apply] at hf
  have hm : ∀ i:ℕ,L (Y i)=_ := fun i=> (show L (Y i)=Y i x from rfl)
  simp_rw [hm,show ∀ i, ‖Y i x‖=_ from fun i=> hY i x, show L O = x from rfl, sub_self,smul_zero] at hf
  have hl:=tendsto_nhds_unique hf tendsto_const_nhds; simp only [ContinuousLinearMap.comp_apply] at hl; change (2:ℕ) • ⟪x,F x⟫=0 at hl; simpa using hl

include hY he H h g in
set_option maxHeartbeats 400000 in
lemma no_arrival (hn : ∀ i,nearest p (Y i)) (hh : Tendsto Y atTop (𝓝 1)) (hv : Tendsto (inspect Y 1) atTop (𝓝 F)): False:=by
  let δ (i:ℕ):= ‖Y i-1‖; have hδ : ∀ i,0<δ i:=fun i=>norm_pos_iff.mpr (sub_ne_zero.mpr (he _)); let u (i:ℕ):= whip F (-(δ i)); let R (i:ℕ):= u i * Y i
  have hg:=deviation Y F hY hh hv
  have hU: Singlet fun T=> differ p T F:=by
    intro T v
    set B:=motor (Ad v) T
    refine tendsto_nhds_unique_of_eventuallyEq (watches hh hv (differ_hit p B)) (watches hh hv (differ_hit p T)) (Eventually.of_forall (fun i=>?_)); dsimp only; rw [show play p B (Y i)=_ from H i T v, show play p B O=play p T O from sings h T v]; rfl
  have hk : Tendsto δ atTop (𝓝 0):=by simpa only [sub_self,norm_zero] using (hh.sub (tendsto_const_nhds (x:=O))).norm
  have hw : Tendsto (fun i=> (δ i)⁻¹ • (R i-1)) atTop (𝓝 0):=by
    have hu : Tendsto (fun i=> (δ i)⁻¹ • (u i-1)) atTop (𝓝 (-F)):= negatives F hk (Eventually.of_forall hδ)
    have hi:= (hu.mul hh).add hv; rw [mul_one,neg_add_cancel] at hi; refine hi.congr fun i=>?_; unfold R
    rw [show u i*Y i-1=(u i-1)*Y i+(Y i-1) by rw [sub_mul]; simp, smul_add]; exact congr_arg (fun z:Motor G=>z+(δ i)⁻¹ • (Y i-1)) (ContinuousLinearMap.ext fun x : G.Color=> rfl)
  have hv' : ∀ᶠ i in atTop, ‖(δ i)⁻¹ • (R i-1)‖ <1 := by apply hw.norm.eventually (gt_mem_nhds (by rw [norm_zero]; norm_num))
  obtain ⟨i,hi⟩:=hv'.exists
  have hup : ∀ T,play p T (u i)=probe T p:=fun T=> stiff F (fun T=> stops g h F hg hU T) T _
  have hwz : tag p (R i) = tag p (Y i):= by funext T; unfold tag play R; rw [motor_mul]; exact hup (motor (Y i) T)
  have hrot : Rot (u i):= arc F hg _
  have hR : ‖Y i -1‖ ≤ ‖R i-1‖:=hn i (R i) ⟨show Rot (R i) from hrot.multiply (hY i),hwz⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hδ i)), ← div_eq_inv_mul, div_lt_one (hδ i)] at hi; exact hi.not_ge hR
end contradiction
end YM.XSpace.Sample
