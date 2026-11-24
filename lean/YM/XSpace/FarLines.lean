import YM.XSpace.CrossLines
import YM.XSpace.Costs
import YM.Next.MAXWELL.Pole

/-!
# Ordinary (periodic) part of order-zero normalized kernel. Off diagonal

Numerical `O(ε)` (kernel, before mesh sums or center
integration). Work along any fixed-stretching regulator, simultaneously on
ANY moving cover-site tuples in fixed compact separated configurations. Beware here
`Far` = off mesh diagonal at fixed physical lengths, NOT probes at increasing
measurement distance. Keep exact weights as in initialization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cross
open Lattice Filter Set Function Exterior Top Expense Further.FreeCovariance.KP
open Next.Rank Beamer Maxwell
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {ι : Type*} {j l : ℕ} {u : Filter ι} {g : ι → Mesh} {x y : ι → Cover}

def far (g : ι→Mesh) (x y : ι→Cover) (i : ι): E4:=a g i • rcast (x i-y i)
lemma views (p : Mesh) (x : Cover): p.coord x=p.spacing • rcast x:=rfl
lemma rcast_add (x y : Cover): rcast (x+y)=rcast x+rcast y:=by ext i; simp [rcast]
lemma rcast_sub (x y : Cover): rcast (x-y)=rcast x-rcast y:=by ext i; simp [rcast]

-- Compact geometry group reused when introducing measurements.
def Rout (u : Filter ι) (x : ι → E4):=∃ δ a:ℝ,0<δ ∧ ∀ᶠ i in u, δ≤‖x i‖ ∧ ‖x i‖≤a
lemma rout_of_compact {K : Set E4} (h : IsCompact K) (hp : K ⊆ away) (p : ι → E4) (ht : ∀ᶠ i in u,p i ∈ K): Rout u p:=by
  by_cases hh : K=∅; · subst K; refine ⟨1,1,one_pos,ht.mono (fun _ h=> False.elim h)⟩
  obtain ⟨x,hx,hL⟩ := h.exists_isMinOn (nonempty_iff_ne_empty.mpr hh) continuous_norm.continuousOn
  obtain ⟨C,hC⟩:=(h.image continuous_norm).bddAbove
  refine ⟨‖x‖,C,norm_pos_iff.mpr (hp hx), ht.mono (fun x hi=> ⟨hL hi,hC (Set.mem_image_of_mem _ hi)⟩)⟩
lemma Rout.alive {p : ι→E4} (h : Rout u p): ∀ᶠ i in u,p i∈away:=by obtain ⟨C,d,hc,H⟩:=h; exact H.mono (fun i hi=> norm_pos_iff.mp (hc.trans_le hi.1))

def ann (δ a : ℝ): Set E4 := Metric.closedBall 0 a\ Metric.ball 0 δ
lemma ann_bands (δ a : ℝ) (x : E4): x∈ann δ a ↔ δ≤‖x‖ ∧ ‖x‖≤a:=by simp only [ann, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right, not_lt]; tauto
lemma ann_away {δ a : ℝ} (h : 0<δ): ann δ a ⊆ away:= fun x hx => norm_pos_iff.mp (h.trans_le ((ann_bands _ _ x).1 hx).1)
lemma ann_compact (δ a : ℝ): IsCompact (ann δ a):= IsCompact.diff (isCompact_closedBall ..) Metric.isOpen_ball
lemma toll (p : ι→E4) (h : Rout u p) (v : Probe G j) (w : Probe G l): Cap u (fun i=> legKernel v w (p i)):=by
  obtain ⟨c,d,hc,H⟩:=h; have he:ContinuousOn (legKernel v w) (ann c d):= fun x hx=> ((kernel_smooth v w (ann_away hc hx)).continuousAt).continuousWithinAt
  refine Cap.includes _ ((ann_compact c d).image_of_continuousOn he) ?_; filter_upwards [H] with i hi; exact Set.mem_image_of_mem _ ((ann_bands ..).2 hi)

lemma shifts (C : Stretched u g) {p : ι → E4} (h : Rout u p) (d : E4) :
    let f:=fun i=> p i+a g i • d; Rout u f ∧ ∀ v : Probe G j,∀ w : Probe G l, Rate u g (fun i=>legKernel v w (f i)) (fun i=>legKernel v w (p i)):=by
  intro f; obtain ⟨δ,r,hδ,H⟩:=h
  let L:=fun i=>a g i • d; have hL : Tendsto L u (𝓝 0):=by unfold L; simpa using (C.endpt.smul_const d)
  have hp:∀ᶠ i in u, f i∈ann (δ/2) (r+δ) ∧ p i∈ann (δ/2) (r+δ):=by
    filter_upwards [H,hL.norm.eventually (ge_mem_nhds (show ‖(0:E4)‖<δ/2 by rw [norm_zero]; linarith))] with i hi he
    unfold f; change ‖L i‖ ≤ δ/2 at he
    rw [ann_bands,ann_bands]; refine ⟨⟨?_,?_⟩,?_,?_⟩
    · have h:= norm_sub_norm_le (p i) (p i+L i); rw [show p i-(p i+L i) = -L i by abel,norm_neg] at h
      change δ/2≤ ‖p i+L i‖; linarith [hi.1]
    · exact (norm_add_le ..).trans (by linarith only [hi.2,(show 0<δ from hδ),he])
    · linarith [hi.1]
    linarith [hi.2]
  refine ⟨⟨δ/2, r+δ,by linarith, hp.mono (fun i hi=> (ann_bands ..).1 hi.1)⟩,fun v w=>?_⟩
  obtain ⟨K,hK⟩:= LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (f:=legKernel (G:=G) v w) (ann_compact (δ/2) (r+δ)) (by
    intro x hx; obtain ⟨B,t,ht,H⟩:= ((kernel_smooth v w (ann_away (by linarith) hx)).of_le (show (1: ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith; exact ⟨B,t,nhdsWithin_le_nhds ht,H⟩)
  refine Rate.introduce (K * ‖d‖) (hp.mono (fun i hi =>?_)); have hh:= hK.dist_le_mul _ hi.1 _ hi.2; rw [dist_eq_norm,dist_eq_norm] at hh; apply hh.trans_eq; unfold f; rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (actual g i).le]; ring

lemma dimensions (p q : Degree G) (C : Stretched u g) (H : Rout u (far g (fun i=>x i+p.point) (fun i=>y i+q.point))) :
    Rate u g (fun i=> ((a g i)⁻¹)^(4+p.degree+q.degree) * mourn (gesture p) (gesture q) (lag (g i).p (x i) (y i)))
      (fun i=> legKernel (actsOn p.degree (gesture p)) (actsOn q.degree (gesture q)) (far g (fun i=>x i+p.point) (fun i=> y i+q.point) i)):=by
  let k:=4+p.degree+q.degree; let M i:= mourn (gesture p) (gesture q) (lag (g i).p (x i) (y i)); let f:=legKernel (actsOn p.degree (gesture p)) (actsOn q.degree (gesture q)); let z i:=rcast (x i+p.point-(y i+q.point)); have hf:= Maxwell.Free.kernel_pole (actsOn p.degree (gesture p)) (actsOn q.degree (gesture q))
  obtain ⟨δ,r,hδ,h⟩:=H; obtain ⟨B,hB,hK⟩:= journey p q
  have ht:= (C.pay (k+2)).eventually_ge_atTop (1:ℝ)
  let C' := ((max r 0)+1)+(δ⁻¹)^(k+1)
  refine Rate.introduce (B*C') ?_; filter_upwards [h,C.smaller,ht,C.endpt.eventually (ge_mem_nhds hδ)] with i hx ha he hp
  let t:= a g i; let w:=z i; let N:=sides g i; have t_pos:0<t:=actual g i; have N_pos : 0<N:=counted g i
  have hx' : δ≤ t*‖w‖ ∧ t*‖w‖≤r:= by rw [← show ‖t • w‖= t*‖w‖ by rw [norm_smul,Real.norm_of_nonneg t_pos.le]]; exact hx
  change t^(k+2)*N ≥ (1:ℝ) at he; change t≤ δ at hp; change t≤1 at ha
  have hw : 1 ≤ ‖w‖ := (mul_le_mul_iff_right₀ t_pos).mp (by rw [mul_one]; linarith only [hp,hx'.1])
  specialize hK (g i).p (x i) (y i) hw
  rw [show 5+p.degree+q.degree=k+1 by unfold k; omega] at hK
  change ‖M i-f w‖ ≤ B*((‖w‖^(k+1))⁻¹+(1+‖w‖)/N) at hK
  have hw':0<‖w‖:=zero_lt_one.trans_le hw
  change ‖t⁻¹^k*M i-f (t • w)‖ ≤ B*C'*t
  change Maxwell.Free.Pole k f at hf; rw [hf.degree t t_pos _ (norm_pos_iff.mp hw'), smul_eq_mul]
  rw [← mul_sub,norm_mul,Real.norm_of_nonneg (pow_pos (inv_pos.mpr t_pos) k).le]
  apply (mul_le_mul_of_nonneg_left hK (pow_pos (inv_pos.mpr t_pos) k).le).trans
  rw [mul_left_comm, mul_assoc B]; apply mul_le_mul_of_nonneg_left _ hB.le
  have h₁:t⁻¹ ^ k * (‖w‖^(k+1))⁻¹ ≤ δ⁻¹^(k+1)*t:= by
    have he:(‖w‖^(k+1))⁻¹≤(δ/t)⁻¹^(k+1):=by rw [inv_pow]; exact (inv_le_inv₀ (by positivity) (by positivity)).2 (pow_le_pow_left₀ (by positivity) ((div_le_iff₀ t_pos).2 (by rw [mul_comm]; exact hx'.1)) _)
    refine (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq ?_; rw [inv_pow, inv_div, div_pow, inv_pow,pow_succ]; field_simp
  have h₂:t⁻¹^k*((1+‖w‖)/N) ≤ (1+r)*t:= by
    calc
      _ ≤ t⁻¹^k*((1+‖w‖)* t^(k+2)):= by rw [div_eq_mul_inv]; gcongr; exact (inv_le_iff_one_le_mul₀ N_pos).2 he
      _ = (t+t*‖w‖)*t:= by rw [pow_add t k 2,inv_pow]; field_simp
      _ ≤ _ := by gcongr; exact hx'.2
  rw [mul_add]; unfold C'; linarith only [h₁,h₂,mul_le_mul_of_nonneg_right (le_max_left r 0) t_pos.le]

lemma off (p q : Degree G) (C : Stretched u g) (H : Rout u (far g x y)):
    Rate u g (fun i=> ((a g i)⁻¹)^(4+p.degree+q.degree)*mourn (gesture p) (gesture q) (lag (g i).p (x i) (y i)))
      (fun i=> legKernel (actsOn p.degree (gesture p)) (actsOn q.degree (gesture q)) (far g x y i)):=by
  let K:=fun i=> a g i • rcast (p.point-q.point); let f i:= far g x y i+K i; let h:= shifts (G:=G) (j:=p.degree) (l:=q.degree) C H (rcast (p.point-q.point))
  have he : far g (fun i=>x i+p.point) (fun i=> y i+q.point)= f:= by funext i; unfold f K far; simp only [add_sub_add_comm (_ : Cover) p.point (y _) q.point, rcast_add, smul_add]
  have hh:= dimensions (x:=x) (y:=y) p q C (he.symm ▸ h.1); apply hh.trans; rw [he]; exact h.2 _ _

lemma blend (C : Stretched u g) (H : Rout u (far g x y)) (L M : Module.Dual ℝ (Horizon G))
    (hl : bright L) (hm : bright M) (hk : Starts j L) (he : Starts l M) :
    Rate u g (fun i=> (a g i)⁻¹^(4+j+l)*mourn L M (lag (g i).p (x i) (y i))) (fun i=>legKernel (actsOn j L) (actsOn l M) (far g x y i)):=by
  obtain ⟨r,s,ha⟩:= removes L hl hk; obtain ⟨t,v,hv⟩:=removes M hm he
  let f (a' : Reading G j r) (b' : Reading G l t) i:= s a' * v b' *((a g i)⁻¹^(4+j+l) * mourn (gesture (mood a')) (gesture (mood b')) (lag (g i).p (x i) (y i)))
  let k (a' : Reading G j r) (b' : Reading G l t) i:= s a' *v b' * legKernel (actsOn j (gesture (mood a'))) (actsOn l (gesture (mood b'))) (far g x y i)
  have hp a b : Rate u g (f a b) (k a b):=(off (mood a) (mood b) C H).const_mul _
  have h: Rate u g (fun i=> ∑ a, ∑ b,f a b i) (fun i=> ∑ a,∑ b,k a b i):= Rate.sum _ _ _ (fun v _=>Rate.sum (f v) (k v) _ fun b _=> hp v b)
  apply h.congr
  · filter_upwards with i; rw [on_mourn _ L M hm (x i) (y i) s ha v hv]; simp only [Finset.mul_sum]; unfold f; congr! 2 with j v; ring
  filter_upwards [H.alive] with i hx; let P:= pairing (G:=G) (j:=j) (l:=l) hx; change _ = P _ _; rw [lowers L s ha,lowers M v hv,map_sum P,LinearMap.sum_apply]; refine Finset.sum_congr rfl fun j _=> ?_; rw [map_smul P,LinearMap.smul_apply, map_sum, Finset.smul_sum]; refine Finset.sum_congr rfl fun b _=> ?_; rw [map_smul]; unfold k; rw [mul_assoc]; rfl
end YM.XSpace.Cross
