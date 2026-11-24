import YM.LocalLTE.FieldPT.Rye
/-! finite jets on lifted Phi. Every degree remains Comic (when vacuum and required
 hypothesis), so clipping individual degrees is covariant and projection-null.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset MeasureTheory
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {j z k m i:ℕ} {W κ K U C V t H: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
lemma Comic.weight {X:RegularAddress n}{p:BudgetPoint}{f:Config G n→ℝ}(h:Comic G X p f) (s:ℝ): Comic G X p (s • f):= by
   refine ⟨AnalyticBridge.CouplingShape.reg_scale _ h.1,by simp [h.2.1],fun hu v w hv hw=> ?_⟩
   have he:=h.2.2 hu v w hv hw; unfold logHessian; unfold logHessian at he; change iteratedFDeriv ℝ (2:ℕ) (s • germ f) 0 _ = _
   rw [iteratedFDeriv_const_smul_apply (germ_diff h.1),_root_.smul_apply]; exact congr_arg (s • ·) he|>.trans (by simp)
lemma Comic.totals {ι:Type*}(s:Finset ι){X:RegularAddress n}{p:BudgetPoint}{f:ι→ Config G n→ℝ}(h:∀ i∈s,Comic G X p (f i)):Comic G X p (∑ i∈s,f i):=by
    induction s using Finset.induction_on with
    | empty=> exact Price.flick p
    | insert i s he ih=> rw [Finset.sum_insert he,← sub_neg_eq_add,← neg_one_smul ℝ]; exact (h i (mem_insert_self ..)).pair ((ih fun j hj=> h j (mem_insert_of_mem hj)).weight _)
open Scene
variable {a:RegularAddress n}(X:Art a z)(p:BudgetPoint)(f:ℝ→Pot G n)(s:ℝ) {r:ℝ}
local notation "L0"=> X.grove
local notation "o"=> a.site
local notation "W"=> X.radius
local notation "g"=> Scene.tallyF X.grove f
open Tensor
local notation "E"=> Directions G n
-- rendering specified slots without labels coalescing.New degree q tested complete Scenes
-- Scaling explicit representation for all marker solver.
def play (κ:ℝ)(u:Tensor.T (Directions G n) ℝ i) := FrameBox.realise L0 W κ (FrameBox.colorP (Pi.single (M:=fun j:Fin (i+1)=>Tensor.T (Directions G n) ℝ j) (Fin.last i) u))
lemma play_cost (U:BudgetPoint){κ V:ℝ}(hp:Reliable G κ V)(T:Tensor.T (Directions G n) ℝ i) : U.Regular a.support (play X κ T):= reg_larger (FrameBox.legal _ _ hp _ _) (Price.color_site X)
lemma playback (u:Tensor.T (Directions G n) ℝ i)(κ:ℝ)(V:Config G n): play X κ u V = ∫ j:G.El, Tensor.diagonal u (FrameBox.wheel j (X.grove.crook W Chi.canonical κ V)) ∂G.probHaar:=by
    unfold play FrameBox.realise; rw [FrameBox.sunwheel]; refine MeasureTheory.integral_congr_ae (ae_of_all _ (fun x=>?_)); unfold Cabana.actual
    dsimp only; rw [Finset.sum_apply, Finset.sum_eq_single (Fin.last i)]; · simp
    · intro j hj ht; rw [Pi.single_eq_of_ne ht]; rfl
    simp
lemma playable (X₁:Tensor.T (Directions G n) ℝ i)(v: Directions G n): Continuous fun u:G.El=>Tensor.diagonal X₁ (FrameBox.wheel u v):= (Tensor.diag_smooth _ ω).continuous.comp (wheel_moves _)
def playL (κ:ℝ)(i:ℕ) : Tensor.T (Directions G n) ℝ i →ₗ[ℝ] (Config G n→ℝ):= {
   toFun := play X κ
   map_add' q p:=by
       funext V; rw [playback]; simp only [Pi.add_apply,playback,Tensor.diagonal,_root_.add_apply]; exact integral_add (μ:=G.probHaar) ((playable q _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ((playable p _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
   map_smul' t q := by
       funext v; rw [playback]; simp only [Pi.smul_apply,playback,Tensor.diagonal,_root_.smul_apply,RingHom.id_apply]; exact MeasureTheory.integral_smul .. }
lemma harmonic (P:Cabana.Pkt (Directions G n) m) (κ:ℝ) : realise X.grove W κ (colorP P) = ∑ i:Fin m, play X κ (P i):=by
   funext i; unfold FrameBox.realise; rw [sunwheel]; unfold Cabana.actual; simp_rw [Finset.sum_apply,playback]; exact MeasureTheory.integral_finsetSum _ (fun i _=> (playable (P i) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) -- edit index
variable (hp:Reliable G κ K)(hf:Scene X.grove κ X.radius k m f C)
include hp hf
lemma ensemble (he:∀ s∈Weft.clip, p.Regular a.support (f s))(s:ℝ)(hs:s∈Weft.clip) : f s = ∑ x:Weft.J k,Weft.mark k x s • ∑ u:Fin m, play X κ (Scene.kernelF X.grove f u.val W x):=by
   let v:= fun i:Fin m=> Scene.tallyF X.grove f i.val X.radius s; have hz:= Scene.recordOne X.grove f X.radius p hf hp s hs
   apply Eq.trans (Scene.invariance X.grove f X.radius p (he _ hs) v hp hz); rw [harmonic]; simp_rw [Finset.smul_sum]; rw [sum_comm]; apply Finset.sum_congr rfl
   intro i hi; have h:= (Scene.invested X.grove f i.val W p hf hp i.isLt).1.seen hs; change playL X κ i.val (Scene.tallyF L0 f i.val W s)=_; rw [h, map_sum]; exact sum_congr rfl (fun i h=> (playL X κ _).map_smul ..)
omit hp hf
open Grove
lemma lowG (u:Tensor.T (Directions G n) ℝ i) (h₂:2 < i)(hp:Reliable G κ K) : Comic G a p (play X κ u):=by
   let x:= Pi.single (M:=fun j:Fin (i+1)=>Tensor.T (Directions G n) ℝ j) (Fin.last i) u
   let K:=FrameBox.colorP x
   have he j (h:j ≠ Fin.last i): K j=0:=by unfold K FrameBox.colorP FrameBox.castP x; simp_rw [Pi.single_eq_of_ne h, show ∀ i':G.El,ContinuousMultilinearMap.compContinuousLinearMap (0:Tensor.T E ℝ j.val) (fun _=>wheel (c:=n) i')=0 from fun _=>by ext; rfl]; simp

   have h: Cabana.actual K=Tensor.diagonal (symmetrize (K (Fin.last i))):= by
       funext v; unfold Cabana.actual; rw [Finset.sum_apply,Finset.sum_eq_single (Fin.last i) (fun j _ hj=> (by rw [he j hj]; rfl)) (by simp),Tensor.symmetrize_diagonal]
   let f:= play X κ u; refine ⟨play_cost X p hp u,?_,fun hz v w hv hw=>?_⟩ -- edit
   · change Cabana.actual K _=_; rw [h,Hall.home X.grove W hp p]; exact ContinuousMultilinearMap.map_coord_zero _ (⟨0,by omega⟩:Fin i) rfl
   unfold logHessian; let V:= X.grove.crook W Chi.canonical κ (G:=G) ∘ increment 1; let L_D:=Tensor.symmetrize (K (Fin.last i)); have he: V 0=0:=by unfold V; rw [Function.comp_apply,Work.G07.at_zero_increment]; exact Hall.home _ _ hp p
   have ht : iteratedFDeriv ℝ 2 ((Cabana.actual K) ∘ V) 0=0:=by
      rw [h]; have hz : ∀ j≤ (2:ℕ), iteratedFDeriv ℝ j (Tensor.diagonal L_D) 0=0:=by
         intro j hj; refine (smul_right_injective _ (show ((j.factorial:ℝ))⁻¹ ≠ 0 from by positivity)) (?_); dsimp only; rw [smul_zero]; exact YM.LocalLTE.under L_D (Tensor.symmetrize_sym _) (lt_of_le_of_lt hj h₂)
      have hL: ContDiffAt ℝ (↑(2:ℕ)) V 0:=Hall.clip_ok W X.grove hp 2 _
      have he:= Work.G05.jets_comp (d:=2) hL hL ((Tensor.diag_smooth L_D _).contDiffAt) (g':=fun _=> (0:ℝ)) contDiffAt_const rfl (fun _ _=>rfl) (x:=0) (fun j hj=> ?_) 2 le_rfl
      · refine he.trans ?_; simp [Function.comp_def];
      rw [show V 0=0 from he,hz j hj]; simp
   change iteratedFDeriv ℝ (2:ℕ) ((Cabana.actual K) ∘ V) 0 _=_; rw [ht]; rfl
end YM.AnalyticBridge.VerifiedReset.Collection.Price
