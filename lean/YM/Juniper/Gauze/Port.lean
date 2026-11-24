import YM.Juniper.Gauze.Marquee
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Views
/-!
 # Gauge integration cost. Compactness, not volume cost
 Demand strict flag-free only; next remove seam criterion and work
 at arbitrary supports so long as mask-certified. -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Gauze
open Filter Function Metric Lattice Wilson RG Push Push.AbsoluteSums
open Pressure Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel SliceRows Coat
open PhysicalNext PhysicalNext.Repeat Boulevard Blaze Brush Sienna
open Uniform Extra.Trajectories MeasureTheory Push.PriceCompiler Blaze.Frond
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge} {c L: Side} {P : BudgetPoint} {J k u:ℕ}
local notation "X"=>Positions (Uniform.Primary c G)
variable {v a b d w e : ℝ}{μ : Measure G.El}
section compact
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](y:E) {f:E×G.Mat→ℝ}{H:E→ℝ}
local notation "v₀"=> ContinuousMultilinearMap.compContinuousLinearMapL
include y
omit y [FiniteDimensional ℝ E] in
private lemma smoothFamily {k : ℕ} {P:Type}[NormedAddCommGroup P][NormedSpace ℝ P]{f:E×P→ℝ} (h : ContDiff ℝ (k:ℕ∞ω) f) :
    Continuous (fun p : E×P=> iteratedFDeriv ℝ k (fun x => f (x,p.2)) p.1) := by
  -- adapt C25 for REAL matrix Hessians
  let T := ContinuousLinearMap.inl ℝ E P
  have he (p : E×P) : iteratedFDeriv ℝ k (fun t => f (t,p.2)) p.1 = v₀ (fun _:Fin k=>T) (iteratedFDeriv ℝ k f p) := by
    let D : E × P→ ℝ := fun y => f ((0,p.2) + y)
    have hD:D ∘ T=(fun t => f (t,p.2)):= by ext t; simp [D,T]
    rw [← hD,T.iteratedFDeriv_comp_right (show ContDiff ℝ ↑k D from (h.comp (contDiff_const.add contDiff_id))) p.1 le_rfl, show D=(fun y => f ((0,p.2)+y)) from rfl, iteratedFDeriv_comp_add_left]
    simp [T]
  simp_rw [he]; exact (v₀ (fun _ : Fin k => T)).continuous.comp (h.continuous_iteratedFDeriv le_rfl)

lemma propolis (hq : ContDiffAt ℝ ↑k H y) (hp : ContDiff ℝ ↑k f) : Meristem (fun x : E=> fun a:G.El=> H x- f (x,G.mat a)) y G.probHaar k:= by
   obtain ⟨C,hC,h⟩:= Brush.neighborhood y hq; obtain ⟨δ,hδ,hΩ⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp h; let P:= closedBall y δ; let Ω:= Set.range G.mat
   haveI : TopologicalSpace.PseudoMetrizableSpace G.Mat:= inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin G.repDim → Fin G.repDim → ℂ))
   have hv (x:E)(he:x∈P):Brush k C 1 H x:= hΩ he; have he (g:G.El): ContDiff ℝ ↑k (fun x:E=> f (x,G.mat g)):= hp.comp (contDiff_id.prodMk contDiff_const)
   let Z:= isCompact_range G.continuous_mat
   refine ⟨P, closedBall_mem_nhds _ hδ, Eventually.of_forall fun a y hy=> (hv y hy).smooth.sub (he a).contDiffAt,fun i hi => ?_⟩
   let R:= fun p:E×G.Mat=> iteratedFDeriv ℝ i (fun x:E=> f (x,p.2)) p.1
   have hR:Continuous R:= smoothFamily (P:=G.Mat) (hp.of_le (Nat.cast_le.mpr hi)); obtain ⟨w,hw⟩:= ((isCompact_closedBall y δ).prod Z).exists_bound_of_continuousOn hR.continuousOn
   have hx (a:G.El)(t:E)(hP:t∈P):iteratedFDeriv ℝ i (fun x:E=>H x-f (x,G.mat a)) t= iteratedFDeriv ℝ i H t-R (t,G.mat a):= by
     apply iteratedFDeriv_sub_apply ((hv _ hP).smaller hi).smooth ((he a).of_le (Nat.cast_le.mpr hi)).contDiffAt
   refine ⟨fun _=> C+w,integrable_const _,fun t ht=> ?_,Eventually.of_forall  (fun a t ht=>?_ )⟩
   · unfold JetF; simp_rw [hx _ t ht]; exact (continuous_const.sub (hR.comp (continuous_const.prodMk G.continuous_mat))).aestronglyMeasurable
   unfold JetF; rw [hx a t ht]; refine (norm_sub_le ..).trans (add_le_add ?_ (hw (t,G.mat a) ⟨ht,Set.mem_range_self _⟩)); simpa only [one_pow,mul_one] using (hv t ht).order i hi
end compact
section ready
variable {T:Snip G}
abbrev minds (k:ℕ) (v:ℝ):= (2:ℝ)^k*((k.factorial:ℝ)*v)

private lemma matHere : ContDiff ℝ ∞ (matrixField (G:=G) (n:=c) ∘ actual):= by
   apply contDiff_pi.mpr; intro i
   have hv:∀ x:X, matrixField (actual x) i=G.mat (G.lieExp (Uniform.tint G _ x (pole i))):= fun x=>by unfold matrixField; rw [Function.comp_apply,Boulevard.actual, Work.F03.represent_link]; rfl
   simp_rw [Function.comp_apply,hv]; exact (G.exp_jet.of_le le_top).comp ((contDiff_apply ..).comp (Uniform.tint G (Body 1 c)).contDiff)
set_option maxHeartbeats 280000 in
lemma locale {F : Config G c→ℝ} {K : Positions (Uniform.Primary c G)→ℝ} (hK:ContDiff ℝ ∞ K)(hq :∀ (V:Config G c),V∈ sunny P →∀ a:G.El, F (castle V a)= F V)
    {M :ℝ→ℕ} {t:ℝ}(he:reshapeG G L T M t P.order)(hf:c.val≤ M t)(hp:∀ w:Positions (Uniform.Primary c G), ‖w‖+2*furl G L t < eaves G L t → actual w∈ sunny P→ Brush P.order v (eaves G L t)⁻¹ (F∘actual-K) w) :
    ∀ w:X,‖w‖+2*furl G L t < slim G L t → actual w∈ sunny P→ Brush P.order (2*minds P.order v) (slim G L t)⁻¹ ((Boulevard.stillA (F-resin T K (c:=c)))∘actual) w := by
   let n:= P.order; let f':= slim G L t; let g:= eaves G L t
   let q (x:X)(a:G.El):= F (actual x)-K (putty T (actual x) a)
   let p:= F-resin T (c:=c) K; let Q:= p∘actual
   have hx:Q=fun x=> ∫ a:G.El, q x a ∂G.probHaar:= by funext x; unfold q; rw [integral_sub (integrable_const _) (integrable_resin (f:=K) T hK.continuous _), integral_const, probReal_univ,one_smul]; rfl
   have hα:= he.1; have hf₀: 0<f':= Real.rpow_pos_of_pos hα _; have he':0<g:= Real.rpow_pos_of_pos hα _; have h':0<furl G L t:=Real.rpow_pos_of_pos hα _
   have h(u:X):ContinuousAt (actual (c:=c) (G:=G)) u:= by
     refine (continuous_pi (fun j=> ?_)).continuousAt; simp_rw [actual,represent_link]; exact G.lieExp_cont.comp ((continuous_apply _).comp (Uniform.tint _ _).continuous)
   suffices h : ∀ (x:X), ‖x‖+2*furl G L t<f' → actual x∈ sunny P→Brush n (minds n v) (f')⁻¹ Q x by
       intro w hw hh; have hv : (actual (0:X))=1:= by rw [actual,map_zero]; exact link_one ..
       have h₀: (1:Config G c)∈sunny P:= fun i=> by simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read, posDir, negDir] using P.threshold_pos
       have hC:= he
       have hQ:= h 0 (by simpa only [norm_zero,zero_add] using he.2.1) (hv.symm ▸ h₀) -- fix heShrink
       change Brush n (2*minds n v) f'⁻¹ (stillA p∘actual) w;rw [two_mul,show stillA p∘actual=(fun i=> Q i-Q 0) from funext (fun i=> by change p (actual i)-p 1=p (actual i)-p (actual 0); rw [hv])]
       exact ((h w hw hh).separating ((certified (inv_nonneg.mpr hf₀.le) (Q 0)).climb hQ.bound le_rfl))
   intro w hw hΨ; let f x:=(matrixField (G:=G) (n:=c) (actual x)); let b (p:X×G.Mat):= K (epoxy T (f p.1) p.2)
   have hyx : ContDiff ℝ ∞ (fun z:X×G.Mat=> (f z.1,z.2)):= (show ContDiff ℝ ∞ (fun z:X×G.Mat=> f z.1) from (matHere (G:=G) (c:=c)).comp contDiff_fst).prodMk contDiff_snd
   have hepp : ContDiff ℝ ∞ (fun z:X×G.Mat=> epoxy T (f z.1) z.2):= by
      have he:= (epoxy_ready (c:=c) T).comp hyx
      simpa only [comp_def] using he
   have hb:ContDiff ℝ ∞ b:= hK.comp hepp
   have hH:=(hp w (hw.trans_le he.2.2.1) hΨ).smooth.add (contDiff_infty.mp hK n|>.contDiffAt)
   rw [hx]; apply Meristem.buds (U:=q) (propolis (G:=G) (H:=F∘actual) w _ (contDiff_infty.mp hb n)) (fun _=> minds P.order v) (integrable_const _) (inv_nonneg.mpr hf₀.le) (by simp [n])
   · refine Eventually.of_forall fun a=>?_ ; obtain ⟨hk,hT,hP⟩:= he.2.2.2 c w hf (by exact (le_add_of_nonneg_right (show 0≤2*furl G L t from mul_nonneg zero_le_two h'.le)).trans hw.le) a
     let p' (x:X):= putty T (actual x) a
     have hc(V:Config G c)(k:Site c→ G.El)(hf: V ∈ sunny P): gauge k V∈ sunny P:= fun i=> by rw [face_gauge,G.chord_conj]; exact hf i -- type inference rw
     have hΦ: actual (p' w)∈ sunny P:= (show castle (actual w) a=actual _ from hT.self_of_nhds) ▸ hc _ _ (hc _ _ hΨ) -- orientation
     apply (storm hk (hp (p' w) hP hΦ) he').shimmy; filter_upwards [hT,(h w) ((sky P).mem_nhds hΨ)] with x hS ht; change q x a = F (actual (p' x))-K _; change castle (actual x) a=actual (p' x) at hS; rw [← hS,hq _ ht]
   have hX : ContDiffAt ℝ ↑n ((F ∘ actual - K)+K) w := hH; rwa [sub_add_cancel] at hX
end ready
end YM.Juniper.Gauze
