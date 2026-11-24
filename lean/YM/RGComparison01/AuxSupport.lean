import YM.RGComparison01.AuxFabric

/-! # Cut to full exchange with extra insertions
 Not a comparison after changing paths. Single fixed analytic coefficient data. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxFabric
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure PhysicalNext.Repeat Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Work.G05
open AuxJets AuxCurtain AuxStage WilsonStartup Tensor AuxConstant Matrix
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
local notation "Y" => Poll.Body ι
local notation "J" => (ℝ×E)
variable {f g : Poll.Body ι→ E→ℝ} {u v a d D h C M : ℝ} {i j k q p m r : ℕ}

section support
omit [DecidableEq ι]
lemma blank (p : Probe f k j q d D C v) (z : Y) : FlatAt q (fun x=> truncate f D x z) 0:= by
  by_cases H:z∈closedBall 0 D
  · exact (p.null z).congr (Eventually.of_forall fun i=> (indicator_of_mem H (fun z=> f z i)).symm)
  rw [show (fun x=> truncate f D x z)=fun y=> 0 from funext fun _=> indicator_of_notMem H _]
  intro i hi; simp
lemma Probe.pays (p : Probe f k j q d D C v) : 0 ≤ v:= by
  have hx:= (p.origin (0:Y)).nonneg; simpa using hx
lemma Probe.raise (p : Probe f k i q d D C u) (hh : C≤M) (hv : u ≤ v) (hi : i ≤ j) (he : r ≤ q) : Probe f k j r d D M v:= by
  refine ⟨p.toBeing, ⟨p.stencil.positive.trans hh,fun i hi=> ⟨(p.stencil.toll i hi).1,fun z=> ((p.stencil.toll i hi).2 z).climb hh le_rfl⟩⟩,fun z=> (p.origin z).climb ?_ le_rfl,fun z i hi=> p.null z i (hi.trans_le he)⟩
  exact mul_le_mul hv (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg z)) hi) (by positivity) (p.pays.trans hv)
lemma Probe.lower (p : Probe f k i q d D C u) (hh : j ≤ k) (he : a ≤ d) : Probe f j i q a D C u:= by
  refine ⟨⟨fun r hr=>?_⟩,⟨p.stencil.positive, fun i hi=> ⟨(p.stencil.toll _ (ball_subset_ball he hi)).1, fun z=> ((p.stencil.toll _ (ball_subset_ball he hi)).2 z).smaller hh⟩⟩,fun z=> (p.origin z).smaller hh,p.null⟩
  obtain ⟨C,h⟩:=p.outer r hr; exact ⟨C,h.mono fun z hz=>⟨hz.1,fun x=>(hz.2 x).smaller hh⟩⟩
lemma Purchase.widen (p : Purchase f k d D a C) (h : a≤v) (hh : C≤u) : Purchase f k d D v u:= ⟨p.positive.trans hh, fun i hi=> ⟨(p.toll i hi).1, fun z=>((p.toll i hi).2 z).climb hh h⟩⟩

lemma Purchase.scalar_mul (w:ℝ) (p:Purchase f k d D a v): Purchase (w • f) k d D a (‖w‖*v):= by
  have hx x : truncate (w • f) D x= w • truncate f D x:= by ext z; by_cases h:z∈closedBall 0 D <;> simp [truncate,h]
  refine ⟨mul_nonneg (norm_nonneg _) p.positive,fun i hi=> ⟨by rw [hx]; exact measurable_const.smul ((p.toll i hi).1),fun z=> (p.toll i hi|>.2 z|>.smul w).shimmy (Eventually.of_forall fun i=> congr_fun (hx i) z)⟩⟩

lemma washed (hp:Probe f k j q d D C v) (hh : q ≤ k) (h : 0<d) (hv : d≤1): Purchase f k d D d⁻¹ (C*d^q):=
    ⟨mul_nonneg hp.stencil.positive (pow_pos h q).le, fun x hx=> ⟨(hp.stencil.toll x hx).1, fun z=> vanishing (fun i hi=> (hp.stencil.toll i hi).2 z) (blank hp z) h hv hh hx⟩⟩
lemma Probe.numeric {t : ℕ} (P : Probe f k j (q+t) (d*h) D C v) (hh: 0 < h) (hv : 0 < d) (hB : d*h≤1) (hq : q+t ≤ k):
    Purchase ((h⁻¹^q) • f) k (d*h) D (d*h)⁻¹ ((C*d^(q+t))*h^t):= by
  have he := Purchase.scalar_mul (h⁻¹^q) (washed P hq (mul_pos hv hh) hB)
  rw [Real.norm_of_nonneg (by positivity : 0≤h⁻¹^q),mul_pow, pow_add h,inv_pow,show (h^q)⁻¹ * (C*(d^(q+t)*(h^q*h^t)))=C*d^(q+t)*h^t from (by field_simp)] at he
  rwa [inv_pow]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma after (F:ℝ→ℝ) {x:E} (h : Measurable (truncate f D x)) (hg : Measurable F) : Measurable (truncate (fun z y=> F (f z y)) D x):= by
  have he : truncate (fun z y=> F (f z y)) D x=(closedBall 0 D).indicator (F ∘ truncate f D x):= by ext z; by_cases H:z∈closedBall 0 D <;> simp [truncate,H]
  rw [he]; exact (hg.comp h).indicator measurableSet_closedBall
lemma read_comp (P : Purchase f k d D C v) (F : ℝ→ℝ) (hg : Measurable F) (hx:0≤u) (H : ∀ y∈ball 0 d, ∀ z∈closedBall (0:Y) D, Brush k u C (fun x=> F (truncate f D x z)) y) : Purchase (fun z y=> F (f z y)) k d D C u := by
  refine ⟨hx,fun x hi=> ⟨after F (P.toll x hi|>.1) hg,fun z=>?_⟩⟩
  by_cases he:z∈closedBall (0:Y) D
  · apply (H x hi z he).shimmy; refine Eventually.of_forall fun i=>?_ ; simp [truncate,he]
  exact (constant (k:=k) (u:=0) (x:=x) (P.toll x hi |>.2 z |>.pos) (by simpa using hx)).shimmy (Eventually.of_forall fun _=> indicator_of_notMem he _)
end support

variable [FiniteDimensional ℝ E]
section relative
variable {ϕ ψ : E×Poll.Body ι→ℝ} {ρ : E→Poll.Body ι} {W:E→Matrix ι ι ℝ}
    (hh : Lantern.Golf ϕ ψ ρ W k D d d C)
local notation "U" => AuxGrace.nodes ϕ ψ ρ W
local notation "F" => Lantern.fee k C D
local notation "B" => Lantern.clump k (F) v
local notation "s" => closedBall (0:Y) D
include hh
lemma shape (h : ∀ x∈Icc (-1:ℝ) 1, Brush k v 1 Real.exp x) (hv : (Lantern.fee k C D)*d≤1) (hk : 1 ≤ k) (ht : 1 ≤ D) : Probe U k (AuxGrace.zgrade k) 0 d D B B := by
  have ht' := h 0 (by norm_num)
  have hw := AuxGrace.buds hh ht ht'; have h0 : 0≤ B:= by simpa using (hw 0).nonneg
  refine ⟨⟨fun d hd=>?_⟩,⟨h0,fun x hx=>?_⟩,hw, fun _ _ h=>(Nat.not_lt_zero _ h).elim⟩
  · obtain ⟨v,-,he⟩:= AuxGrace.neighbors hh hd ht; exact ⟨v,he⟩
  have he := mem_ball_zero_iff.mp hx; have hF : ‖x.2‖ < d:= (_root_.norm_snd_le x).trans_lt he; have hX:= (_root_.norm_fst_le x).trans_lt he
  refine ⟨Lantern.duties _ hh hF hX,fun z=>?_⟩
  by_cases H:z∈s
  · have hz:=mem_closedBall_zero_iff.mp H; exact (Lantern.composite (Lantern.compel _ hh hF hX hz) (h _ (Lantern.ether _ hh hF hX hk (by simpa using hv) z hz))).shimmy (Eventually.of_forall fun _=> indicator_of_mem H _)
  exact (constant (k:=k) (x:=x) (u:=0) zero_le_one (by simpa using h0)).shimmy (Eventually.of_forall fun _=> indicator_of_notMem H _)
end relative

section kernel
-- full output coefficient *at order i*; p finite suppressed from name
variable {f : Poll.Body ι → ℝ×E → ℝ}
local notation "µ" => Poll.sweep Q
local notation "s" => closedBall (0:Y) D

def readsH (Q:Matrix ι ι ℝ) (f:Y→(ℝ×E)→ℝ) (q:ℕ): AuxStage.Co E:=
    fun i=> ritual (AuxConstant.mean (i+q) Q f) q i
lemma order_indep (P : Probe f k j r d D u v) (hq : Q.PosDef) (he: ∀ z:ι→ℝ,dotProduct z (Q*ᵥ z) ≤ a*dotProduct z z)
    (hD : 0 ≤ D) (hi:p ≤ k) :
    (∀ j,j ≤ p → Integrable (AuxConstant.moment f j) µ) ∧ ∀ i, i+q ≤ p →
      ritual (AuxConstant.mean p Q f) q i = readsH Q f q i := by
  have hv:= (P.lower hi le_rfl).toBeing; have hw:= bookF
  let b(i:ℕ):=AuxConstant.mean i Q f
  have hh i (H:i ≤ p) : ∀ z:Y, ContDiffAt ℝ (↑i) (f z) 0:= fun z=> (P.origin z|>.smaller (H.trans hi)).smooth
  refine ⟨hw,fun i hi=>?_⟩; ext1 x
  change Tensor.diagonal (Tensor.coeff (b p) (i+q) 0) _ =Tensor.diagonal (Tensor.coeff (b _) _ 0) _
  unfold b Tensor.coeff; rw [AuxConstant.reads f hi hw (hh p le_rfl),AuxConstant.reads f (le_refl (i+q)) (fun i h=> hw i (h.trans hi)) (hh _ hi)]
where
  bookF i (hi:i ≤ p) : Integrable (AuxConstant.moment f i) µ:= by
    have ht:= AuxConstant.upgrades f hq he P.pays (fun _ hr=> (P.toBeing.buys hr)) P.origin (le_refl _) hD; exact ht.1 _ (hi.trans ‹p ≤ k›)
omit [FiniteDimensional ℝ E] in
lemma reads_null (P : Probe f k j r d D u v) (hz : i+q < r) : readsH Q f q i=0:= by
  -- mean polynomial: every coeff integrated is zero, with or without asserting existence
  have hb l (hl:l ≤ i+q) : (fun z:Y=> Tensor.coeff (f z) l 0)=fun _=>0:= by funext z; unfold Tensor.coeff; rw [P.null z _ (hl.trans_lt hz), smul_zero]
  have he : AuxConstant.mean (i+q) Q f=0:= by
    unfold AuxConstant.mean; refine Finset.sum_eq_zero (fun a hh=> ?_); rw [MeasureTheory.integral_congr_ae (Eventually.of_forall (fun z=> congr_fun (hb a (Nat.le_of_lt_succ (Finset.mem_range.mp hh))) z))]; simp_rw [integral_zero]; rfl
  ext x; unfold readsH ritual; rw [he]; simp [Tensor.diagonal,Tensor.coeff]

lemma estimates (P : Probe f k j q (d*h) D u v) (hp : p+q < k) (hk : m ≤ k) (hq : Q.PosDef) (he : ∀ z:ι→ℝ,dotProduct z (Q*ᵥ z) ≤ a*dotProduct z z) (hD : 0 ≤ D) (H : ∫ z in sᶜ, (1+‖z‖)^j ∂µ ≤ h^(p+q+1)) (hh : 0 < h) (hv : 1 < d) (hc : d*h≤1) : ∀ x:E, ‖x‖ < d*h →
    AuxStage.Points (ritual_fee q p u v d) ((d*h)⁻¹) h p m (fun x:E=> h⁻¹^q * intake Q f D (h,x)) x (readsH Q f q):= by
  have ht : ∀ y∈ball 0 (d*h), Brush k u 1 (intake Q f D) y:= fun y hy=> (at_center P.stencil Q y hy).2
  have hp' := P.lower hp.le le_rfl
  let B:= AuxConstant.mean (p+q) Q f
  obtain ⟨hr,hQ⟩:=AuxConstant.upgrades f hq he P.pays (fun D H=> hp'.toBeing.buys H) hp'.origin H hD
  have hB:=AuxConstant.mean_contDiff (p+q) f Q; have hf:=order_indep (q:=q) P hq he hD hp.le
  have hf (i:ℕ) (hi:i ≤ p) : headAt (ritual B q) h i=headAt (readsH Q f q) h i:= by ext x; unfold headAt; unfold B; rw [hf.2 i (by omega)]
  have hy : FlatAt q B 0:= by
    intro i hi; rw [show iteratedFDeriv ℝ i B 0=_ from AuxConstant.reads f (by omega : i ≤ p+q) hr (fun z=> (hp'.origin z).smooth),show AuxConstant.moment f i=fun _=>0 from funext fun z=> P.null z _ hi]; simp
  intro x hx; have he:= ritual_P hp hk (hB _|>.contDiffAt) hy hh hv hc hx ht hQ
  constructor
  · intro i hi; rw [← hf i hi]; exact he.bill i hi
  refine he.tail.shimmy (Eventually.of_forall fun i=>congr_arg (fun y=>h⁻¹^q * intake Q f D (h,i)-y) (Finset.sum_congr rfl fun j hj=>congr_fun (hf j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).symm i))
end kernel
end YM.RGComparison01.AuxFabric
