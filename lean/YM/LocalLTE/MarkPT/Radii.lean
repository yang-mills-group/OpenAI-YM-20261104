import YM.LocalLTE.FieldPT.Leaf
import YM.LocalLTE.Quartz.Core
/-!
 ETCHED payload billed from true Lifetime. This is a LOCAL convention:
 E sector grade interpreted as a prescribed normalization `grain`. Inputs to this
 strict step are actual release stencils from the preceding step (or birth)
 in price-tagged order. No need to assume they transport in some ideal
 scheme. Here MARK branch is governed by entry heights, then pay unscaling after selection of whole gas. Other possible Laurent regulators welcomed as below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Function Lattice RG Pressure Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side}
open Fan Brush Foramen Pastel
variable {v z r C w s t y η γ B a ε α κ K: ℝ} {j n m k N M : ℕ}
open Weft AnalyticBridge.VerifiedReset FrameBox Tensor
local notation "E"=> Directions G c
namespace Scene
variable {o: Site c} (X:Grove o) (FF: Config G c→ℝ)(i l K:ℕ)
variable (p:BudgetPoint) {K1:ℝ}
lemma tracks₀ (n:ℕ) (b κ:ℝ) (P:Cabana.Pkt (Directions G c) (i+1)) (he:∀ u:Fin (i+1), ‖(b^u.val/b^n) • P u‖ ≤ C): Scene X κ l (n+i+1) (i+1) (fun s=>Scene.branch X s l n b κ P) C:= by
   let G0:=G; let n':=n; let Z(j: Fin (i+1)):= (b^j.val/b^n') • P j
   let g(s:ℝ) : Cabana.Pkt (Directions G c) (i+1):= s^n' • (fun j=> (s^j.val)⁻¹ • Z j)
   have hx s: Scene.branch X s l n b κ P= FrameBox.realise X l κ (g s):=by funext u; unfold FrameBox.realise g Scene.branch; rw [Cabana.actual_smul]; unfold Z; simp_rw [smul_smul]; rfl
   simp_rw [hx]; have hc:0≤C:= (norm_nonneg _).trans (he 0); refine ⟨hc,?_,fun s hs=>⟨_,rfl,fun j=>?_⟩⟩
   · refine Hex.invert fun x=> ?_; unfold realise Cabana.actual; simp_rw [Finset.sum_apply]; refine Hex.total Finset.univ fun j _=> ?_; let nT:= n+i+1; let t:= nT+n'-j.val; have hp:j.val≤nT:=by unfold nT; omega
     refine (Hex.held (k:=nT) ⟨t,by unfold t nT n'; omega⟩ (Tensor.diagonal (Z j) (X.crook l Chi.canonical κ x))).change fun s hs=>?_
     dsimp only; unfold mark Tensor.diagonal
     unfold g; rw [Pi.smul_apply,smul_smul]; rw [_root_.smul_apply, show s^t/s^nT=s^n'*(s^j.val)⁻¹ from ?_]; swap; · rw [← div_eq_mul_inv,div_eq_div_iff (pow_ne_zero _ hs.1.ne') (pow_ne_zero _ hs.1.ne'),← pow_add,← pow_add]; congr 1; unfold t; omega
     rfl
   have h_:0 < s:=hs.1
   unfold g; rw [Pi.smul_apply,smul_comm (s^j.val),smul_inv_smul₀ (pow_ne_zero _ h_.ne'),norm_smul,Real.norm_of_nonneg (pow_nonneg h_.le _)]; exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ h_.le hs.2)).trans (he j)
lemma harvestM (G:Gauge)(d:ℕ){κ k:ℝ}(hp:Reliable G κ k)(L:Side): ∃ M:ℝ→ℝ, Rate G L 0 M∧∀ᶠ x in atTop,0≤ M x∧∀ c:Side,∀ s:ℝ, betaF G x L/2 ≤ s→ s≤2*betaF G x L → ∀ (p:BudgetPoint)(m:ℕ),p.threshold=Pressure.fiery G x L →∀ (o:Site c)(X:Grove o)(P:Cabana.Pkt (Directions G c) (d+1))(ξ:ℝ)(v:Support c), 0 ≤ ξ→p.supBounds o v (FrameBox.realise X m κ P) ξ →let g:= gStep s
      ∀ i:Fin (d+1), ‖(g^i.val) • FrameBox.clear X m P i‖ ≤ ξ*M x :=by -- via Cabana.price
    obtain ⟨U,hU,hA⟩:= Grove.sound_ball G (χ:=Chi.canonical) hp
    choose C hC hV using fun i:Fin (d+1)=> Cabana.price (d+1) i
    let g(x:ℝ):=2*gStep (betaF G x L)
    let u(x:ℝ):= (U*Pressure.fiery G x L)⁻¹; let M(i:Fin (d+1)) (x:ℝ):= g x^i.val *(C i * (u x)^i.val)
    have hv:Rate G L (1/2) u:= by unfold u; simpa only [_root_.mul_inv_rev] using! ((inverse_mist G L).mul_right U⁻¹)
    have he (i):Rate G L 0 (M i):= (((PhysicalNext.Repeat.Sienna.glim G L).pow i.val).mul ((hv.pow i.val).mul_left (C i))).weaken (by simp)
    let Z x:= ∑ i,|M i x|
    refine ⟨Z, fuelReel M he univ,?_⟩
    filter_upwards [Delay.shift_pos G L] with x hx
    refine ⟨Finset.sum_nonneg fun _ _=> abs_nonneg _,fun c t ht _ p m hh o X P ξ v hz hr i=>?_⟩
    let F:=FrameBox.clear X m P; let s:= U*Pressure.fiery G x L; have hs:0<s:=mul_pos hU (hh ▸ p.threshold_pos); have hθ:= hA c p o X m
    have hP: ‖F i‖ ≤ C i * ξ* s⁻¹^i.val:= hV _ _ _ _ _ (FrameBox.cleans _ _ _) hs hr.1 fun y hy=> (?_) -- edit
    swap
    · obtain ⟨he,hZ⟩:= hθ y (show ‖y‖≤U*p.threshold from hh.symm ▸ hy)
      have hk:= hr.2 _ (hZ.mono_left (Finset.subset_univ v)) [] (by simp) (by simp); change ‖Cabana.actual P _‖ ≤ _ at hk; rw [show FrameBox.Grove.crook X m Chi.canonical κ _= X.shore m y from he] at hk; exact (le_of_eq (congr_arg _ (FrameBox.rays ..))).trans hk
    have hb:=PhysicalNext.Repeat.Sienna.lamp G L hx t ht
    rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hb.1.le _)]
    apply (mul_le_mul (pow_le_pow_left₀ hb.1.le hb.2 i.val) hP (norm_nonneg _) (pow_nonneg (hb.1.le.trans hb.2) _)).trans
    have ht:= (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun i=> |M i x|) (fun _ _=>abs_nonneg _) (Finset.mem_univ i)) hz); apply le_trans _ ht
    refine (le_of_eq (by unfold M; dsimp only [u,s]; ring : _= ξ*M i x)).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hz)
end Scene
open PhysicalNext.Repeat
structure Caption {q:Rep G c}(M:Lotus.Leaf q) (κ:ℝ)(i k j:ℕ) (v:ℝ→ Pot G c)(W:ℝ): Prop where
    scope : ∃ u:ℕ, M.turn=Lotus.Wing.logKey u ∧ Fan.CanX κ i k j v (q.activities.reg u).site (M.weight*W)
structure TurnMark {q:Rep G c}(M:Lotus.Leaf q) (κ:ℝ)(i j:ℕ)(v:ℝ→ Pot G c)(f: Config G c→ℝ) : Prop where
    bill : ∃ (n u:ℕ)(X:Grove (q.activities.reg n|>.site))(P:Cabana.Pkt (Directions G c) (j+1)),u≤ i∧ M.turn=Lotus.Wing.logKey n ∧ f=FrameBox.realise X u κ P∧v= (fun s=>Scene.branch X s u 0 (gStep q.beta) κ (FrameBox.clear X u P))
lemma woveT {k₁:ℝ}(G:Gauge)(j:ℕ)(L:Side)(hk:Reliable G κ k₁)(K:ℕ)(hK:j+1≤K):∃ V:ℝ→ℝ,Rate G L 0 V ∧∀ᶠ t in atTop, 0 ≤ V t∧∀ (c:Side)(R:Rep G c), R.p.threshold=Pressure.fiery G t L → R.beta ∈ Set.Icc ((betaF G t L)/2) (2*betaF G t L) →∀ (M:Lotus.Leaf R)(u:ℕ)(p:Pot G c), Fan.Mind M p κ j u→∃ Φ:ℝ→ Pot G c, Caption M κ u K (j+1) Φ (V t)∧ TurnMark M κ u j Φ p ∧ Φ (gStep R.beta)=p:=by
    obtain ⟨f,hF,H⟩:= Scene.harvestM G j hk L
    refine ⟨f,hF,?_⟩; filter_upwards [H, Delay.shift_pos G L, (PhysicalNext.Repeat.Sienna.glim G L).below (by norm_num) 1 zero_lt_one] with t ht h hp
    refine ⟨ht.1,fun c R hR hx M u p hp'=> ?_⟩
    obtain ⟨i,hi,hc,-,m,hm,X,P,rfl⟩:= hp'.health
    have hP:= ht.2 c R.beta hx.1 hx.2 R.p m hR _ X P _ M.crest M.profit hc
    let v:= gStep R.beta; let Q':= FrameBox.clear X m P; let Φ:=fun s:ℝ=> Scene.branch X s m 0 v κ Q'
    have hV:(0+j+1)≤ K:=by omega
    have hU:= (Scene.tracks₀ X j m _ v κ Q' (by simpa only [pow_zero,div_one] using hP)).generous _ hV le_rfl
    have hb:= PhysicalNext.Repeat.Sienna.lamp G L h R.beta hx.1
    exact ⟨Φ,⟨i,hi,⟨m,hm,X,hU⟩⟩,⟨i,m,X,P,hm,hi,rfl,rfl⟩,Scene.recovered X m _ ⟨hb.1,hb.2.trans ((le_abs_self _).trans hp)⟩ _ _ _⟩
end YM.LocalLTE.Weft
