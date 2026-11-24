import YM.OPE.Compatible.Scrape.Gate
import YM.Next.RANK.Terrain
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Gear
/-!
# Chart derivative entitlement
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Next.Rank Next.Rank.Spindle Source WilsonStartup Gauge Next.Fluctuations Metric
open MultiNext.SignedSource MultiNext.SignedSource.Lyre MultiNext.SignedSource.Mom
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X:Type*}{n:Side}(o:Site n){b i k r m:ℕ}
lemma composeL [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup X][NormedSpace ℝ X]{F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](L:E→L[ℝ] X)(f:X→F){x:E}(h:ContDiffAt ℝ r f (L x)): iteratedFDeriv ℝ r (f ∘ L) x=(iteratedFDeriv ℝ r f (L x)).compContinuousLinearMap (fun _=> L):=by
      -- Mathlib within version
      obtain ⟨S,hS,hU,hX⟩:= _root_.mem_nhds_iff.mp (h.eventually (by simp)); have he:ContDiffOn ℝ r f S:=fun y hy=> ((show ContDiffAt ℝ (↑r) f y from hS hy)).contDiffWithinAt
      let T:= L ⁻¹' S; have hp:IsOpen T:=hU.preimage L.continuous; have hz:x∈T:=hX; have hh:= L.iteratedFDerivWithin_comp_right he hU.uniqueDiffOn hp.uniqueDiffOn hX (by exact le_rfl : (r:ℕ∞ω)≤r); rwa[iteratedFDerivWithin_of_isOpen _ hp hz,iteratedFDerivWithin_of_isOpen _ hU hX] at hh -- name
abbrev mill (K:BudgetPoint)(F:Config G n→ℂ): Directions G n→ℂ:= (F ∘ increment 1) ∘ (K.threshold • ContinuousLinearMap.id ℝ (Directions G n))
abbrev DanceU (h:2*(b+1)<n.val)(K:BudgetPoint): DrawerB G b→ Directions G n:= K.threshold⁻¹ • ((Steer o h) ∘ (K.threshold • ContinuousLinearMap.id ℝ (DrawerB G b)))
abbrev HeadU (h:2*(b+1)<n.val)(K:BudgetPoint)(F: Config G n→ℂ):= (mill K F) ∘ (DanceU o h K)
lemma revalue (h:2*(b+1)<n.val)(K:BudgetPoint)(F: Config G n→ℂ)(x): HeadU o h K F x= F (motorB o h (K.threshold • x)):=congrArg (F ∘ increment 1) (smul_inv_smul₀ K.threshold_pos.ne' _)
def Widen (K:BudgetPoint)(b:ℕ):Prop:= K.threshold*(1+(b:ℝ))^K.power≤1
lemma geV (k:ℕ)(G:Gauge):∃ C:ℝ,1 ≤ C∧∀ (n:Side) (o:Site n)(x:Directions G n)(K:BudgetPoint)(b:ℕ)(F:Config G n→ℂ)(τ:ℝ), (∀ i,‖K.threshold • x i‖ ≤1) → Healthy K.threshold (Spindle.patch b o) (increment 1 (K.threshold • x)) → Widen K b→ k ≤ K.order → K.Regular (Spindle.patch b o) F → K.supBounds o (Spindle.patch b o) F τ → ‖iteratedFDeriv ℝ k (mill K F) x‖ ≤ C* τ:=by
      obtain ⟨C,hC,h⟩:= Lyre.general k 1 G; refine ⟨C,hC,fun n o x K b F τ hv hh hW hi hF hp=>?_⟩
      let L:= K.threshold • ContinuousLinearMap.id ℝ (Directions G n); have he:ContDiffAt ℝ k (F ∘ increment 1) (L x):=(responsive 1 K hF hh).of_le (Nat.cast_le.mpr hi)
      change ‖iteratedFDeriv ℝ k ((F∘increment 1) ∘ L) x‖ ≤ _; rw [composeL L _ he]; apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (zero_le_one.trans hC) hp.1); intro v; have hz (i:Fin k): Sized ‖v i‖ (L (v i)) K o:=by
           refine ⟨norm_nonneg _,fun j=>?_⟩; change ‖K.threshold • v i j‖≤ _; rw [norm_smul_of_nonneg K.threshold_pos.le]; refine (mul_le_mul_of_nonneg_left (norm_le_pi_norm ..) K.threshold_pos.le).trans ?_; rw [mul_comm K.threshold]; exact mul_le_mul_of_nonneg_left (by unfold width; exact le_mul_of_one_le_right K.threshold_pos.le (one_le_pow₀ (by simp))) (norm_nonneg _)
      have ha (e:Edge (Site n))(he:needed (Spindle.patch b o) e):width K o e≤1:=by
           have hx: separation e.1 o≤ b:=by rw [separation_comm]; exact (doors _).1 he.1
           exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ 1+(separation e.1 o:ℝ) from by positivity) (show 1+(separation e.1 o:ℝ)≤1+b from by gcongr) _) K.threshold_pos.le).trans hW
      exact (h n (Spindle.patch b o) K o (L x) F 1 τ (L∘v) (fun i=>‖v i‖) hi hF hh hp (fun i hi=>⟨hv i,ha i hi⟩) hz).trans_eq (by ring)
variable (P:Pad G)(h:2*(b+1)<n.val) (K:BudgetPoint)
local notation "Λ"=> DrawerB G b
lemma sob_h (x:Λ)(hv:‖x‖≤ P.r): ContDiffAt ℝ ω (DanceU (G:=G) o h K) x:=by
     let L:= K.threshold • ContinuousLinearMap.id ℝ (DrawerB G b); have hx : ‖L x‖≤P.r:= (norm_smul_of_nonneg K.threshold_pos.le x).trans_le ((mul_le_of_le_one_left (norm_nonneg _) K.threshold_le).trans hv); exact ContDiffAt.const_smul (K.threshold⁻¹) ( (fris o P h hx).comp (f:=L) x L.contDiff.contDiffAt )
lemma hence (x:Λ)(hv:‖x‖≤P.r):Healthy K.threshold (Spindle.patch b o) (increment 1 (K.threshold • DanceU o h K x)) :=by
     rw [show increment 1 (K.threshold • DanceU o h K x)=motorB o h (K.threshold • x) from congr_arg (increment 1) (smul_inv_smul₀ K.threshold_pos.ne' _)]; unfold Healthy; rw [mainR _ P h K.threshold_pos.le K.threshold_le hv]; simp
lemma glaze (x:Λ)(hv:‖x‖≤P.r) (i):‖K.threshold • DanceU o h K x i‖≤ 1:= by
     rw [show K.threshold • DanceU o h K x i=Steer o h (K.threshold • x) i from congr_fun (smul_inv_smul₀ K.threshold_pos.ne' (Steer o h (K.threshold • x))) i]
     exact P.small _ ((sizeTD o i h _).trans ((norm_smul_of_nonneg K.threshold_pos.le x).trans_le ((mul_le_of_le_one_left (norm_nonneg _) K.threshold_le).trans hv)))
lemma Ch_k (F:Config G n →ℂ)(hF:K.Regular (Spindle.patch b o) F) (x:Λ)(hv:‖x‖≤P.r):ContDiffAt ℝ K.order (HeadU o h K F) x:=by
     let L:= K.threshold • ContinuousLinearMap.id ℝ (Directions G n); exact ((responsive 1 K hF (hence o P h K x hv)).comp (f:=L) _ L.contDiff.contDiffAt).comp _ ((sob_h o P h K x hv).of_le le_top)
lemma danceν (P:Pad G)(k:ℕ)(hv:0 < k):∃ D:ℝ,1≤D ∧∀ (n:Side)(b:ℕ)(K:BudgetPoint)(o:Site n)(h:2*(b+1)<n.val)(x: DrawerB G b), ‖x‖ ≤ P.r→ ‖iteratedFDeriv ℝ k (DanceU o h K) x‖ ≤ D:=by
     let f(y:G.Color):= iteratedFDeriv ℝ k (undo G) y; let S:=closedBall (0:G.Color) P.r; have he:ContinuousOn f S:= fun y hy=> ((P.analytic y (mem_closedBall_zero_iff.mp hy)).continuousAt_iteratedFDeriv le_top).continuousWithinAt
     obtain ⟨D,hD⟩:=(isCompact_closedBall ..).exists_bound_of_continuousOn he
     let C:=max 1 D; have hz:1≤ C:=le_max_left ..; refine ⟨C,hz,fun n b K o h x ht=> ContinuousMultilinearMap.opNorm_le_bound (zero_le_one.trans hz) (fun v=>?_)⟩
     let A:=DanceU (G:=G) o h K; let q(i):Directions G n→L[ℝ] G.Color:= ContinuousLinearMap.proj i; let U:=K.threshold; have hU:0<U:=K.threshold_pos; apply (pi_norm_le_iff_of_nonneg (mul_nonneg (zero_le_one.trans hz) (Finset.prod_nonneg (fun _ _=> norm_nonneg _)))).2; intro i; let L: DrawerB G b→L[ℝ] G.Color:= U • offsetDir o h i; have hL(y:DrawerB G b): ‖L y‖≤ U*‖y‖:= (norm_smul_of_nonneg hU.le _).trans_le (mul_le_mul_of_nonneg_left (sizeTD o i h _) hU.le)
     have hp(y:DrawerB G b): q i (A y)=U⁻¹ • undo G (L y):=by change _=U⁻¹ • undo G (U • offsetDir o h i y); rw [←map_smul];rfl
     have hN:‖L x‖≤P.r:=(hL x).trans ((mul_le_of_le_one_left (norm_nonneg _) K.threshold_le).trans ht)
     have hg:=P.analytic (L x) hN
     change ‖q i (iteratedFDeriv ℝ k A x v)‖≤_
     have h₁:=DFunLike.congr_fun ((q i).iteratedFDeriv_comp_left (sob_h o P h K x ht) (show (k:ℕ∞ω) ≤ ω from le_top)) v; rw [show (q i) (iteratedFDeriv ℝ k A x v)=_ from h₁.symm, show (q i) ∘ (DanceU o h K)=U⁻¹ • ((undo G) ∘ L) from funext hp]; rw [iteratedFDeriv_const_smul_apply ((hg.comp (f:=L) x L.contDiff.contDiffAt).of_le le_top),composeL L _ (hg.of_le le_top)]; change ‖(U⁻¹:ℝ) • (f (L x) (L ∘ v))‖≤_
     rw [norm_smul_of_nonneg (inv_pos.mpr hU).le]; let a:= ∏ i,‖v i‖; have hb : 0≤a:=Finset.prod_nonneg fun _ _=> norm_nonneg _; have ha:∏ i,‖L (v i)‖≤ U*a:=(Finset.prod_le_prod (fun j _=> norm_nonneg _) (fun j _=> hL (v j))).trans (by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right ((pow_le_pow_of_le_one hU.le K.threshold_le (show 1 ≤ k from hv)).trans_eq (pow_one _)) hb)
     exact (mul_le_mul_of_nonneg_left (((f (L x)).le_opNorm (L ∘ v)).trans (mul_le_mul ((hD (L x) (mem_closedBall_zero_iff.mpr hN)).trans (le_max_right ..)) ha (Finset.prod_nonneg fun _ _=>norm_nonneg _) (zero_le_one.trans hz))) (inv_pos.mpr hU).le).trans_eq (by change U⁻¹*(C*(U*a))=_; rw [mul_left_comm C,inv_mul_cancel_left₀ hU.ne'])
end YM.OPE.Spells
