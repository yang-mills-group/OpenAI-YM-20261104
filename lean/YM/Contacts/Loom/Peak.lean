import YM.Contacts.Loom.Iris
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
variable {x:Frame α E}{d:ℕ→ℝ}{S:Lamp F}{u:Shelf E α F}
open PertExtension.Series Radial Milling
open Tensor (diagonal)
structure Root (N:Meter)(S:Lamp F) (k:ℕ)(p:ℝ) (d:ℕ→ℝ):Prop where
  price: Budget N (Frame.Port F d) k p (fun i _=>S i)
  analytic : ∀ᶠ i in atTop, AnalyticAt ℝ (S i) 0
namespace Rush
lemma reV {Y:ℕ→ℝ} (h: N.Funds (fun i b=> ‖Y i‖≤ b) p): N.Rush p Y:= by obtain ⟨f,hf,hg⟩:=h.cap; exact hf.view (hg.mono fun i hi=> hi.2.trans_eq (Real.norm_of_nonneg hi.1).symm)
lemma normV (hp:N.Rush p f): N.Rush p fun i=> ‖f i‖:= absolute hp
lemma absSq (hp:N.Rush p f): N.Rush (2*p) (fun i=> f i^2) := by simpa [mul_comm, sq] using hp.times hp (show p+p=2*p by ring) -- simp big
lemma shrinking {d:ℕ→ℝ}(h:N.Rush p f)(ht:N.Rush q fun i=>(d i)⁻¹)(hd:∀ᶠ i in atTop,0< d i) (he:p+q<0): ∀ᶠ i in atTop,f i<d i:= by
   filter_upwards [sliding (h.times ht rfl) he _ zero_lt_one,hd] with i hi hd; exact lt_of_mul_lt_mul_right (a:=(d i)⁻¹) ((le_abs_self _|>.trans_lt hi).trans_eq (mul_inv_cancel₀ hd.ne').symm) (inv_nonneg.mpr hd.le) -- rw
end Rush
variable {σ:ℝ}
structure Pouch (N:Meter)(p:ℝ) (d:ℕ→ℝ) : Prop where
   pos: ∀ᶠ i in atTop,0< d i
   forward : N.Rush p d
   back : N.Rush (-p) (fun i=>(d i)⁻¹)
lemma Pouch.small (h:Pouch N p d)(hp:p<0): ∀ᶠ i in atTop,d i ≤ 1:= (sliding h.forward hp _ zero_lt_one).mono fun i hi=> (le_abs_self _).trans hi.le
lemma Pouch.canon : Pouch N p (N.pow p) := ⟨N.eventual.mono (fun i hi=>Real.rpow_pos_of_pos hi _), Rush.any, (Rush.any (p:=-p)).take (N.eventual.mono fun i hi=> (Real.rpow_neg hi.le _).symm)⟩
lemma Pouch.bank (h:Pouch N p d)(hv: Budget N x k r u)(he:r<p): ∀ᶠ i in atTop, ∀ j, ‖u i j (x i j)‖ < d i := by
   obtain ⟨K,hr,hK⟩:= (Arms.pick_const hv).cap; filter_upwards [hK, Rush.shrinking hr h.back h.pos (by linarith)] with i hi hr j using (hi.2 j).trans_lt hr
-- nonnegative.Arm well.Support.Summability.Var.Cap projection.F.
lemma Frame.head (h: N.Rush p d): N.Funds (fun i t=> ∀ j:↥(Bank E d i), ‖Port E d i j‖≤t) p:= by
   refine ⟨_,(absolute h),Eventually.of_forall fun i=> ⟨abs_nonneg _,fun j=> (mem_ball_zero_iff.mp j.property).le.trans (le_abs_self _)⟩⟩ --
lemma Budget.flag {y:ℕ→ℝ}(h:Arms N x k p d u)(hy:y=ᶠ[atTop] d): Arms N x k p y u:= h.lift le_rfl (hy.mono (fun i hi b hb hr x=> (hi.symm ▸ hr x)))
lemma Budget.collapse (h:Arms N x k p d u)(ht:N.Rush 0 d): Budget N x k p u:= by
   obtain ⟨f,hf,H⟩:= h.cap; let g i:= f i*(1+|d i|)^k; have hh: N.Rush p g:= hf.times (((Rush.settle 1).blend (absolute ht)).powers k) (by ring); refine ⟨_,hh,H.mono fun i hi=> ?_⟩; exact ⟨mul_nonneg hi.1 (by positivity),fun j=> ((hi.2 j).climb le_rfl (le_abs_self _)).trim⟩
lemma Arms.confirm {v :Shelf E α F}(h:∀ᶠ i in atTop, v i=u i)(hr: Arms N x k p d u): Arms N x k p d v:= hr.reveal (h.mono fun i hi j=> (by rw [hi])) le_rfl le_rfl

namespace Root
variable [∀ i, FiniteDimensional ℝ (F i)] (h:Root N S k p d)(he:Pouch N q d)
include h he
lemma worth (hp:j≤k): N.Rush p (fun i=> normJ j (S i) 0):= by
   obtain ⟨f,hf,H⟩:= h.price.cap; exact Rush.reV (Y:=fun i=> normJ j (S i) 0) ⟨_,hf,(H.and he.pos).mono fun i hi=> by simp only [normJ,norm_norm]; exact ⟨hi.1.1, ((Brush.offer.1 (hi.1.2 ⟨_, mem_ball_self (x:=(0:F i)) hi.2⟩)).inside j hp)⟩⟩ -- binder M
lemma tips (hh : l ≤ k+1)(hq:q<0): Root N (fun i=> skel (S i) l) k p d:= by
   have hp: N.Funds _ 0:= (Frame.head (E:=F) (he.forward.mono hq.le)); refine ⟨?_, Eventually.of_forall (fun i=> skel_analytic _ _ _)⟩; exact Budget.skew (j:=l) (w:=S) (Budget.id (x:=Frame.Port F d) hp) le_rfl (fun i hi=> worth h he (by omega))
omit he
lemma moonlit {A:Lamp F}(ht:Root N A k p d) : Root N (S-A) k p d:= ⟨Arms.sub h.price ht.price,(h.analytic.and ht.analytic).mono fun i hi=> hi.1.sub hi.2⟩
include he
lemma snap (ht:j≤k)(hv:∀ᶠ i in atTop, ∀ l<j,iteratedFDeriv ℝ l (S i) 0=0)(hk:q<0): Arms N (Frame.Port F d) k (p+q*j) (fun i=>(d i)⁻¹) (fun i _=>S i):= by
   obtain ⟨f,hf,H⟩:= h.price.cap; refine ⟨_,hf.times (he.forward.powers j) rfl,?_ ⟩; filter_upwards [hv,H,he.pos,he.small hk] with i hi hx hp h'; refine ⟨mul_nonneg hx.1 (pow_nonneg hp.le _),fun x=>?_⟩; have hx x (h:x∈ ball (0:F i) (d i)):= hx.2 ⟨x,h⟩; simpa only [mul_zero,add_zero] using! Shellac.pools (n:=k) (k:=j) hp h' ht (show 0 ≤ f i by have hr:=(hx 0 (mem_ball_self hp)).nonneg; exact hr) (b:=0) le_rfl (fun y hy=> (hx _ hy).smooth) (fun i h hi x hx'=> (Brush.offer.1 (hx _ hx')).2 i hi) (fun l hl=>by rw [normJ,hi l hl]; simp) _ x.property
lemma reminder (ht:j≤k)(hk:q<0): Arms N (Frame.Port F d) k (p+q*j) (fun i=>(d i)⁻¹) (fun i _=> S i-skel (S i) j):= by
   refine (h.moonlit (h.tips he (by omega) hk)).snap he ht (h.analytic.mono ?_) hk; intro i hi; exact (YM.Stationary.rays_jet (hi.sub (skel_analytic ..)) j).1 (cords _ _ hi)
omit h he
lemma application (h:Arms N (Frame.Port F d) k p (fun i=>(d i)⁻¹) (fun i _=> S i)) (hv: ∀ᶠ i in atTop, ∀ j,‖u i j (x i j)‖ < d i) (hp:Pouch N q d)(hc:Budget N x k r u)(hq:r ≤ q): Budget N x k p (fun i j=> S i ∘ u i j) := by
    refine Budget.compose (g:=fun i j=> S i) (Arms.port h ?_) hp.pos hc hp.back ?_
    · exact hv.mono fun i hi j=> mem_ball_zero_iff.mpr (hi j)
    linarith
end Root
end
end YM.Contacts.Loom
