import YM.RG01.Kernel.Journey
/-!
# All orders conditional derivative license on arbitrary held fields

In particular there is no moving-measure assumption. Derive both the
conditional law's smoothness in coarse fields and a uniform cost for
arbitrary configurations over simultaneous perturbations summing to
at most 1/(β κ tariff(G)) in link space. This answers probability-norm
derivative queries on localized supports (also with insertions whose
fine physical *whole-rep expectation* factor is controlled in sup,
pre-renormalization). For blanket position-growing direction prices, must
then prove localization/density-normalized control; not attempting to
buy the inverse of the whole partition or even that of a full coarse
eval. Use pullback secants/context budgets separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Kernel
open Function Filter Set MeasureTheory Complex Metric Topology Finset Lattice RG Wilson Matrix
open ConnectedActivityE6.Blaze Brush WardBin.Lies Wheel
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} (H:History G){N n m j:ℕ} (h:H.Selected)(V:Config G (H.S.side m n))(hm:m<N)
local notation "S0"=> H.levels.clock.op m n
variable {F:(H.levels.clock.op m n).Choices→ Config G (H.S.side (m+1) n)→ℂ}{b:ℝ}(hb:Bounded (prior ..) F b)(hx:0 ≤ b)

def den (V':Config G (H.S.side m n)):ℂ:=(H.rep N n m|>.eval V':ℝ)/(H.rep N n m|>.eval V:ℂ)

include h hm hb hx
private lemma allGerms (k:ℕ): let f := (conditional H N m n · F)
    Germ k (den (N:=N) H V) V ∧ Germ k f V :=by
  intro f
  let A:= S0; let w:=expense H N m n V; let μ:=prior G (H.S.side (m+1) n)
  let Z:=channel A (H.β N n (m+1)) 1 V
  let σ:=generating w Z μ
  have he:=booked A (H.β N n (m+1)) (fun _=>1) V (H.levels.blocks m n|>.branches) (fun i=>zero_le_one)
  have hC:=actual N H h V hm
  have ht : AnalyticAt ℂ (σ 1) 0:=he.entire hC (F:=(1:_)) (b:=1) ⟨fun _=> aestronglyMeasurable_const,fun _ _=>le_of_eq norm_one⟩ zero_le_one 0 (Set.mem_univ _)
  have hX : σ 1 0=1:=Wheel.base hC
  have hU: AnalyticAt ℂ (σ F/σ 1) (0):=(he.entire hC hb hx 0 (Set.mem_univ _)).div ht (by rw [hX]; exact one_ne_zero)
  let X:= fun p=> encoded 1 V (increment V p)
  have hp (i:Edge (Site (H.S.side m n)))(p): X p i=peel (G.lieExp (p i)):= by
    unfold X encoded increment peel; simp
  have hz:X 0=0:=by ext1 i; rw [hp]; change peel (G.lieExp 0)=(0,0); simp only [G.mat_lieExp_zero,peel,G.mat_one,sub_self,star_zero]; rfl
  have hA : ContDiffAt ℝ (↑k) X 0:= by
    apply contDiffAt_pi.mpr; intro i
    simp_rw [hp]
    let L:(Directions G _) →L[ℝ]G.Color:=ContinuousLinearMap.proj i
    have he:‖L‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> (by rw [one_mul]; exact norm_le_pi_norm x i))
    have hf:= peeling (E:=Directions G _) ([L]) (1:ℝ) k zero_le_one (by simp [he])|>.smooth
    convert! hf using 1; ext1 x; rw [steps]; simp [L]
  have hD: (den (N:=N) H V ∘ increment V)= σ 1 ∘ X := by
    funext p
    dsimp only [Function.comp_apply,den,σ,X]; rw [trade H h V hm (1:_) _ _ (by simp)]
    rw [show conditional H N m n _ 1= _ from (actual N H h _ hm).unit,mul_one]
  have hF: (f ∘ increment V)= (σ F /σ 1) ∘ X:= by
    funext p; exact (quotaReal H h V hm _ (fun _=>1) (increment V p) (by simp)).symm
  refine ⟨?_,?_⟩
  · unfold WardBin.Lies.Germ; change ContDiffAt ℝ _ ((den (N:=N) H V)∘ _) _; rw [hD]; apply ContDiffAt.comp _ _ hA
    rw [hz]; exact ht.contDiffAt.restrict_scalars ℝ
  unfold WardBin.Lies.Germ; change ContDiffAt ℝ _ (f ∘ _) _; rw [hF]; apply ContDiffAt.comp _ _ hA
  rw [hz]; exact hU.contDiffAt.restrict_scalars ℝ

def compensation (G:Gauge)(k:ℕ) (b v:ℝ):= ((k.factorial:ℝ)*b*(1+v)^k)*((1+saved k k G)*(2*k:ℝ))^k

theorem controlled (l:List (Directions G (H.S.side m n)))(e:Edge (Site (H.S.side m n))→ℝ)(he:∀ i, 0 ≤ e i)(hv:∀ i,e i≤1)(hL:∀ a∈l,∀ i,‖a i‖≤e i)
    (hη : |H.β N n (m+1) * H.levels.clock.kernel.penalty| * tariff G*(∑ i,e i) ≤ 1):
    let _S:=(H.levels.clock.op m n)
    let f:= fun U=>conditional H N m n U F
    let k:=l.length
    Germ k f V ∧ ‖leftDerivs (den (N:=N) H V) l V‖ ≤ compensation G k 1 1 ∧
      ‖leftDerivs f l V‖ ≤ compensation G k (invoice k b) (1+2*1) :=by
  intro s f k
  obtain ⟨hD,hF⟩:=allGerms H h V hm hb hx k
  obtain ⟨L,hX,hΛ⟩:= follow V l.get e he hv (fun a i=> hL _ (List.get_mem ..) i) k
  let A:=s; let w:=expense H N m n V; let μ:=prior G (H.S.side (m+1) n)
  let Z:=channel A (H.β N n (m+1)) e V
  let σ:=generating w Z μ
  have hC:=actual N H h V hm
  have hE:=booked A (H.β N n (m+1)) e V (H.levels.blocks m n|>.branches) he
  have hQ := (hE.receipt hC hb hx k).climb (show _≤_ from le_rfl) (e:=1+2*1) (add_le_add hη (mul_le_mul_of_nonneg_left hη (by norm_num : (0:ℝ)≤2))) -- climb arg e,b
  have h'₀ : Brush k 1 1 (σ 1) 0:= (hE.rawBrush hC (b:=1) (show Bounded μ (1:_) _ from ⟨fun _=>aestronglyMeasurable_const,fun _ _=>le_of_eq norm_one⟩) zero_le_one k).climb le_rfl hη
  let Y:= fun t=>encoded e V (journey V k l.get t)
  have ht (t:Fin k): ‖(cart t)‖=1:= by rw [cart, Pi.norm_single,norm_one]
  have hP (C:Config G (H.S.side m n)→ℂ)(h : Germ k C V) (W:Angles G (H.S.side m n)→ℂ)(p r:ℝ)(hh:Brush k p r W 0)(hU:C ∘ journey V k l.get = W ∘ Y): ‖leftDerivs C l V‖ ≤ compensation G k p r := by
    have he := L.pine (g:=W) (x:=0) (show Brush k _ 1 W (Y 0) from hX ▸ hh.trim) -- hX cast
    have hk : leftDerivs C l V=iteratedFDeriv ℝ k (W ∘ Y) 0 cart:=by
      rw [← hU]
      simpa only [k,List.ofFn_get] using Germ.ordered l.get h
    rw [hk]; apply ((iteratedFDeriv ℝ k (W ∘ Y) 0).le_opNorm cart).trans
    simp_rw [ht,prod_const_one,mul_one]
    unfold compensation; simpa only [mul_assoc] using! he.order k le_rfl
  refine ⟨hF,hP _ hD _ _ _ h'₀ ?_, hP _ hF _ _ _ hQ ?_⟩
  · funext t; unfold den σ generating; dsimp only [Function.comp_apply]; unfold Y
    have h := trade H h V hm 1 e (journey V k l.get t) (hΛ t)
    rw [show conditional H N m n (journey V k l.get t) 1=_ from (actual N H ‹_› (journey V k l.get t) hm).unit,mul_one] at h
    exact h.symm
  funext t; exact (quotaReal H h V hm _ _ _ (hΛ t)).symm

/-- A ledger at arbitrary weights for probability norm of conditional
coarse derivative outputs. E.g. evaluating output probes through a patch
P of the service with anchored directions, substitute
  e i=threshold*(1+(Dmax:ℝ))^power
on all adjusted bonds with Dmax the max separation from the anchor, zero
elsewhere. Keeps also analytic denominator costs prior to any projections.
 -/
def bill (e:Edge (Site (H.S.side m n))→ℝ)(N m':ℕ) := (1+|H.β N n m'*H.levels.clock.kernel.penalty| * tariff G) * (1+∑ i,e i)

-- uniform for weight scaling at actual β on the trajectory
lemma angular (l:List (Directions G (H.S.side m n)))(e:Edge (Site (H.S.side m n))→ℝ)(he:∀ i, 0 ≤ e i)(hL:∀ a∈l,∀ i,‖a i‖≤e i):
    let T:=bill H e N (m+1)
    let f:= fun U=>conditional H N m n U F
    let k:=l.length
    Germ k f V ∧ ‖leftDerivs (den (N:=N) H V) l V‖ ≤ T^k*compensation G k 1 1 ∧
      ‖leftDerivs f l V‖ ≤ T^k*compensation G k (invoice k b) (1+2*1) :=by
  intro t f k
  have h1 :0≤ tariff G:=zero_le_one.trans (fee G)
  have hE:0≤ ∑ i,e i:=Finset.sum_nonneg fun i _=>he i
  let A:=|H.β N n (m+1) * H.levels.clock.kernel.penalty|
  have ha:0≤A:=abs_nonneg _
  have ht:1≤t:=by change _ ≤ (1+A*tariff G)*(1+_); nlinarith [mul_nonneg ha h1,mul_nonneg (mul_nonneg ha h1) hE]
  let v i:= e i/t; let d(a:Directions G (H.S.side m n)):= t⁻¹ • a
  have hy:0<t:= zero_lt_one.trans_le ht
  have hv :∀ i,v i ≤ 1:=fun i=> (div_le_one hy).mpr ((Finset.single_le_sum (s:=univ) (f:=e) (fun i _=> he i) (mem_univ i)).trans (by
    change _≤ (1+A*tariff G)*(1+_); nlinarith only [mul_nonneg ha h1,mul_nonneg (mul_nonneg ha h1) hE]))
  have hh :∀ a∈ l.map d,∀ i, ‖a i‖≤ v i:= by
    rintro a ha; obtain ⟨z,hz,rfl⟩:= List.mem_map.mp ha
    intro i; unfold d v; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (by positivity),div_eq_mul_inv,mul_comm]; exact mul_le_mul_of_nonneg_right (hL _ hz i) (by positivity)
  have hp:A*tariff G*∑ i,v i ≤ 1:= by
    unfold v; rw [← Finset.sum_div,← mul_div_assoc,div_le_one hy]; change _≤(1+A*tariff G)*(1+_)
    nlinarith only [mul_nonneg ha h1,hE]
  obtain ⟨h,h',h0⟩:= controlled H h V hm hb hx (l.map d) v (fun i=>by unfold v; positivity [he i]) hv hh hp
  rw [List.length_map] at h h' h0
  have hD {n':Lattice.Side}(g:Config G n'→ℂ)(V:Config G n')(l:List (Directions G n'))(c:ℝ):leftDerivs g (l.map (c • ·)) V = c^l.length • leftDerivs g l V:=by
    induction l generalizing V with
    | nil=>simp [leftDerivs]
    | cons a l ih=>
      simp_rw [List.map_cons,leftDerivs,ih,smul_smul,mul_comm _ c]
      rw [deriv_fun_const_smul_field,show deriv (fun t => leftDerivs g l (increment V ((c*t) • a))) 0 = _ from deriv_comp_mul_left c (fun t=>leftDerivs g l (increment V (t•a))) 0,mul_zero,smul_smul,List.length_cons,pow_succ]
  unfold d at *; simp_rw [hD _ _ l t⁻¹, norm_smul] at h' h0
  have he : ‖t⁻¹^l.length‖=(t^l.length)⁻¹:=by rw [inv_pow,Real.norm_of_nonneg]; positivity
  rw [he, inv_mul_le_iff₀ (pow_pos hy _)] at h' h0
  exact ⟨h,h',h0⟩

/-- Cut support convention for consumer evaluating probability derivatives.
(Apply `Layouts` to reclose into a smaller address without the card*diam
loss; here paid deliberately late and explicitly, for any localized capture
or halo operation that needs all k at the stipulated union.) -/
abbrev probePrice (p:BudgetPoint) (o: Site (H.S.side m n)) (z: Finset (Edge (Site (H.S.side m n)))) (N) := bill H (fun i=> if i∈z then p.threshold*(1+(separation i.1 o:ℝ))^p.power else 0) N (m+1)
lemma located (p:BudgetPoint) (o: Site (H.S.side m n)) (z:Finset (Edge (Site (H.S.side m n)))) (l:List (Directions G (H.S.side m n))) (hy:∀ v∈l, p.dirBound o v ∧ ∀ i∉z,v i=0):
    let s:=probePrice H p o z N
    let f:=fun U=>conditional H N m n U F; let k:=l.length
    ‖leftDerivs (den (N:=N) H V) l V‖ ≤ s^k*compensation G k 1 1 ∧
      ‖leftDerivs f l V‖ ≤ s^k*compensation G k (invoice k b) (1+2*1):= by
  intro s f k
  let e(i : Edge (Site (H.S.side m n))) := if i∈z then p.threshold*(1+(separation i.1 o:ℝ))^p.power else 0
  apply (angular H h V hm hb hx l e (fun i=> by unfold e;split; have ht:=p.threshold_pos; positivity; rfl) (fun v h i=>?_)).2
  unfold e; split; next=> exact (hy v h).1 i
  next h₁=> rw [(hy v h).2 i h₁,norm_zero]
end YM.RG01.Kernel
