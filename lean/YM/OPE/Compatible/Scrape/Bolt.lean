import YM.OPE.Compatible.Scrape.Cogn
import YM.OPE.Compatible.Scrape.Wees
/-!
# f0 pallet, downstream of actual entry before horizontal Laplace steps
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Next.Rank Next.Rank.Spindle Source WilsonStartup Gauge Next.Fluctuations Metric Beamer
open MultiNext.SignedSource Lyre Mom Pill
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X:Type*}{n:Side}(o:Site n){b i k r m:ℕ}
abbrev sizeQ (b:ℕ):= 1+(Fintype.card (TilesB b):ℝ)
noncomputable def burnU {b:ℕ}(z: DrawerB G b):ℝ:=∑ i,‖z i‖^2
lemma burnsm (G:Gauge)(b:ℕ):ContDiff ℝ ⊤ (burnU (G:=G) (b:=b)):=by
       exact ContDiff.sum (fun i _=> (((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:TilesB b=>G.Color) i).contDiff).norm_sq ℝ))
lemma burnnn (z:DrawerB G b): 0≤burnU z:=Finset.sum_nonneg fun _ _=>sq_nonneg _
lemma burnlo (z:DrawerB G b){a:ℝ}(he:0≤a)(hx:burnU z≤ a^2): ‖z‖ ≤ a:=by
       apply (pi_norm_le_iff_of_nonneg he).2; intro i; exact le_of_pow_le_pow_left₀ (by norm_num) he ((Finset.single_le_sum (fun j _=> sq_nonneg ‖z j‖) (Finset.mem_univ i)).trans hx)
lemma burnhi (z:DrawerB G b): burnU z≤ sizeQ b*‖z‖^2:=by
       have hz:=Finset.sum_le_sum (s:=Finset.univ) (f:=fun i:TilesB b=>‖z i‖^2) (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) 2); simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hz; exact hz.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (sq_nonneg _))
lemma brisk (z: DrawerB G b)(v:G.El): burnU (crevy v z)=burnU z:= Finset.sum_congr rfl (fun i _=>congrArg (·^(2:ℕ)) (G.norm_adjoint v (z i)))
noncomputable abbrev Swirl (P:Pad G): ContDiffBump (0:ℝ):=⟨P.r^2/2,P.r^2,by have h:=P.pos; positivity,by have h:=pow_pos P.pos 2;linarith⟩
lemma decoy (P:Pad G)(z:DrawerB G b): Swirl P (burnU z)≠0→‖z‖≤ P.r:=by
       intro h; have he:burnU z∈_:= (show burnU z∈tsupport (Swirl P) from subset_closure (show burnU z∈support (Swirl P) from h)); rw [ContDiffBump.tsupport_eq] at he; exact burnlo _ P.pos.le ((Real.le_norm_self _).trans (mem_closedBall_zero_iff.mp he))
lemma minted (P:Pad G)(z:DrawerB G b)(hx:burnU z ≤ P.r^2/2):Swirl P (burnU z)=1:= ContDiffBump.one_of_mem_closedBall _ (mem_closedBall_zero_iff.mpr ((Real.norm_of_nonneg (burnnn z)).trans_le hx)) -- implicit
noncomputable def LaunchB (P:Pad G) (h:2*(b+1)<n.val)(K:BudgetPoint)(f:Config G n→ℂ)(x:DrawerB G b):ℂ:=((Swirl P (burnU x)):ℝ) • HeadU o h K f x
abbrev StartP (P:Pad G)(h:2*(b+1)<n.val)(K:BudgetPoint)(f:Config G n→ℂ)(x:DrawerB G (4*b)):ℂ:=LaunchB o P h K f (socket b x)
lemma stirC (h:2*(b+1)<n.val)(x: DrawerB G b)(u:G.El)(e:Edge (Site n)): offsetDir o h e (crevy u x)= G.adjoint u (offsetDir o h e x):=by unfold offsetDir; split; rfl; simp
lemma HearthY (P:Pad G)(h:2*(b+1)<n.val)(K:BudgetPoint)(F:Config G n→ℂ)(hF:GaugeInvariant F)(x:DrawerB G b)(u:G.El): LaunchB o P h K F (crevy u x)= LaunchB o P h K F x:=by
       simp_rw [LaunchB,brisk]; by_cases hz: Swirl P (burnU x)=0
       · rw [hz,zero_smul,zero_smul]
       apply congr_arg; rw [revalue,revalue,show motorB o h _=Lattice.gauge (fun _=>u) (motorB o h _) from ?_]; exact hF _ _
       funext i; unfold Lattice.gauge; rw [cssh,cssh]; have hv:= decoy P x hz; rw [←map_smul (crevy u), show WingB o h (crevy u _) i=_ from stirC o h (K.threshold • x) u i]; apply P.rotates; exact (sizeTD o i h _).trans ((norm_smul_of_nonneg K.threshold_pos.le x).trans_le ((mul_le_of_le_one_left (norm_nonneg _) K.threshold_le).trans hv))
lemma smooth2B (P:Pad G)(h:2*(b+1)<n.val)(K:BudgetPoint)(F: Config G n→ℂ)(hx:K.Regular (Spindle.patch b o) F):ContDiff ℝ K.order (LaunchB o P h K F):=by
       apply contDiff_iff_contDiffAt.mpr; intro x; let L:=Swirl P; by_cases he:‖x‖≤P.r
       · have hg:ContDiff ℝ (↑(K.order:ℕ∞)) ⇑L:= ContDiffBump.contDiff (f:=Swirl P); have hv:= hg.comp (f:= (burnU : DrawerB G b→ℝ)) ((burnsm G b).of_le le_top); exact hv.contDiffAt.smul (Ch_k o P h K F hx x he)
       refine contDiffAt_const (c:=(0:ℂ)) |>.congr_of_eventuallyEq ?_; filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds (lt_of_not_ge he))] with i hi; rw [LaunchB,show L (burnU i)=0 from not_not.mp fun h=>not_lt.mpr (decoy P i h) hi,zero_smul]
end YM.OPE.Spells
