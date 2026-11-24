import YM.LocalLTE.Weft.Valued
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Higher
/-! paying finite valuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)
open Weft AnalyticBridge.VerifiedReset
local notation "K"=> Disk G c
private lemma clear₂ {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{f:E→F}(h:f 0=0)(he: fderiv ℝ f 0=0)(j:ℕ) : Weft.Null 2 j f := by
    intro i _ hi; apply norm_le_zero_iff.mp; rcases (show i=0 ∨ i=1 from by omega) with h'|h' <;>subst i
    · rw [norm_iteratedFDeriv_zero,h,norm_zero]
    rw [norm_iteratedFDeriv_one,he,norm_zero]
lemma workIvy (H:G.Simple) (hp:P.Funds S T) (z : Air f G)(p:Stream c f) (hu:DifferentiableAt ℝ (twig X z) 0)(hS:DifferentiableAt ℝ (orbitΛ (G:=G) (S:=S) p.1) 0) (hV:DifferentiableAt ℝ (ivy T X.x (choice p.1 X.k) p.2) 0)
    (ht:∀ k∈ parents p.2,DifferentiableAt ℝ (fun v:K=> strain (timeΛ X v) p.1 k (voltage (timeΛ X v))) 0) (j:ℕ): Null 2 j (sourceΛ X p z):=by
   let q:=twig X z; let f:=orbitΛ (S:=S) p.1 ∘ q; let u:= ivy T X.x (choice p.1 X.k) p.2; have hh:f 0=0:=by unfold f q; rw [Function.comp_apply,twig0 X hp]; exact norm_le_zero_iff.mp ((orbitingΛ (S:=S) p.1 _).trans_eq (norm_zero : ‖(0:ZipP G c _)‖=0))
   have he : DifferentiableAt ℝ f 0:= (show DifferentiableAt ℝ _ (q 0) from (by rw [show q 0=0 from twig0 X hp _]; exact hS)).comp _ hu
   have hv: HasFDerivAt (𝕜:=ℝ) (u∘f) 0 0:= by
       have hv0: fderiv ℝ u (f 0)=0:=hh.symm ▸ criticalV H (choice p.1 X.k) p.2 X.x hp hV; have hz:= (show DifferentiableAt ℝ u (f 0) from hh.symm ▸ hV).hasFDerivAt.comp 0 he.hasFDerivAt; rwa [hv0,_root_.ContinuousLinearMap.zero_comp] at hz
   let S(k:Rod c _) (v:K):=strain (timeΛ X v) p.1 k (voltage (timeΛ X v)); have hk k:S k 0=0:=by unfold S; rw [volt0 X hp, show timeΛ X 0=X.blank from ?_, strain0 hp]; unfold timeΛ Vine.pass dry; simp only [Prod.snd_zero,Work.G07.at_zero_increment]; rfl
   let P(k:Rod c _) (v:K):= ‖S k v‖^2 /2; let K':=parents p.2
   have hx: sourceΛ X p z= u ∘ f + ∑ j∈K',P j:=by
       funext v; unfold sourceΛ; rw [Pi.add_apply,Finset.sum_apply]; apply congr_arg₂ (· + ·) (rfl: u (f v)=u (f v)); apply sum_congr rfl fun k hk=> ?_; exact (if_pos (X.blank_all p.1 (spot _ k)): Vine.pot (timeΛ X v) p.1 k _=_) -- edit
   rw [hx]; refine clear₂ (?_) (?_) j
   · rw [Pi.add_apply, Function.comp_apply, hh,show u 0=0 from valence₀ hp ..,Finset.sum_apply]; simp [P,hk]
   have hh (k:Rod c _) (hg:k∈K'): HasFDerivAt (𝕜:=ℝ) (P k) 0 0:= by
      let v:=S k; have ht:= (ht k hg).hasFDerivAt
      have hy: P k= (fun x=> inner ℝ (S k x) (S k x)/2):=funext fun _=> by unfold P; rw [real_inner_self_eq_norm_sq]
      have hf:= ht.inner ℝ ht; change HasFDerivAt _ (fderivInnerCLM _ (S k 0,S k 0) ∘L _) _ at hf; rw [hk,show fderivInnerCLM ℝ ((0:G.Color),0) =0 from ?_, _root_.ContinuousLinearMap.zero_comp] at hf
      · rw [hy]; simpa only [smul_zero,mul_comm,div_eq_mul_inv] using! (hf.const_mul (2:ℝ)⁻¹) -- edit
      exact ContinuousLinearMap.ext fun x=>by simp

   have hg:= hv.add ((HasFDerivAt.fun_sum (u:= K') hh)); -- edit
   simpa only [sum_const_zero,add_zero, Finset.sum_fn] using hg.fderiv
open Extra.Iteration.Derivs
lemma chargeAtom (H:G.Simple)(z : Air f G)(hp : P.Funds S T) (A:ℕ→ Atom G (m+1))(i:Trans f)(b:ℝ) (Q:BudgetPoint)(j:ℕ) (hv:(A i.2.2).Invariant) {p:ℝ} (hh:Mode (Lattice.pull i.1 0 ∘ inputΛ X z) (0:K) (max 1 n) p) : Null 2 j (atomΛ X A i b z) := by
   -- supply chart from composed U ambient Mode, flat gradient via canonical regular
   let F:= (A i.2.2); let f:Config G _ → ℝ:= fun U=> F.unmasked U i.2.1; let q:= Lattice.pull i.1 0 ∘ inputΛ X z; have he:q 0=1:=by
      unfold q inputΛ; rw [Function.comp_apply,twig0 X hp,shaft0]; funext i'; rw [Channel.charge]; simp
   have hg : Q.Regular (F.footprint i.2.1) f := canonical_regular F _ Q hv
   have hW : f 1=0:= by
       simp [f,F,Atom.unmasked,Atom.poly,atSite_path, WilsonStartup.face_one]
   let P(v:K) : Directions G _:= fun i=> G.plog (G.mat (q v i));
   have hP i: ContinuousAt (fun x=>q x i) 0:= by
       let H:= G.continuous_mat.isClosedEmbedding G.mat_injective; exact H.isEmbedding.isInducing.tendsto_nhds_iff.mpr (hh.atLink i|>.smooth.continuousAt)
   have hx: P 0=0:=by unfold P; rw [he]; simp; rfl
   have he': DifferentiableAt ℝ P 0:= (show ContDiffAt ℝ 1 P 0 from (by
       apply contDiffAt_pi.mpr; intro i; let g(x:K):=G.mat (q x i); exact (show ContDiffAt ℝ 1 G.plog (g 0) from (by simp only [g,he,Pi.one_apply,G.mat_one]; exact G.plog_diff.of_le le_top)).comp _ ((hh.atLink i).smooth.of_le (by exact_mod_cast (le_max_left 1 _))))).differentiableAt one_ne_zero
   refine clear₂ (?_) (?_) _; · change b*f (q 0)=0; rw [he,hW,mul_zero]
   have he : q=ᶠ[𝓝 0] increment (1:Config G _) ∘ P:=by
       filter_upwards [eventually_all.mpr fun i=> (show Tendsto (fun x:K=> q x i) (𝓝 0) (𝓝 1) from by have hm:= show Tendsto (fun x:K=> q x i) (𝓝 0) (𝓝 (q 0 i)) from hP i; simpa [he] using hm).eventually G.plog_right] with x hx; funext i; change _= G.lieExp _ * 1; rw [mul_one]; exact (hx i).symm
   have hK : HasFDerivAt (𝕜:=ℝ) ((f ∘ increment 1)∘P) 0 0:=by
      have ht:= (show DifferentiableAt ℝ (f∘increment 1) (P 0) from hx.symm ▸ (germ_diff hg).differentiableAt (by decide)).hasFDerivAt.comp 0 he'.hasFDerivAt; rw [hx, show fderiv ℝ (f∘increment 1) 0=0 from flat_critical H hg,_root_.ContinuousLinearMap.zero_comp] at ht; exact ht
   change fderiv ℝ (fun i=> b*f (q i)) 0=0
   simpa only [smul_zero] using! ((hK.const_mul b).congr_of_eventuallyEq (he.mono fun i hi=> congr_arg (fun U=>b*f U) hi)).fderiv -- edit
end YM.LocalLTE.Fan
