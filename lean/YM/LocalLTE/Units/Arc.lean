import YM.LocalLTE.Units.Oracle
/-! Iterate serialized germs. Generation of invariant representatives via colour averaging.
Certificate doesn't require support rectification of torsion periods. Orthogonality after Movement. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side} {o q : Site c} {m d j:ℕ}
open Cabana Grove
local notation "E"=> Directions G c

def wheel (u:G.El) : E →L[ℝ] E:= ContinuousLinearMap.pi (fun i=> (G.adjoint u).toContinuousLinearMap ∘L ContinuousLinearMap.proj i)
lemma wheel_prod (u v:G.El) (x : E) : wheel (u*v) x=wheel u (wheel v x):= funext fun _=> G.adjoint_mul ..
lemma wheel_norm (u:G.El) (x:E) : ‖wheel u x‖≤‖x‖:=by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=>?_ ; change ‖G.adjoint u _‖≤_; rw [norm_adjoint]; exact norm_le_pi_norm x _
@[fun_prop] lemma wheel_moves (x:E): Continuous fun u:G.El=> wheel u x:=continuous_pi fun i=> show Continuous fun u:G.El=> G.adjoint u (x i) from
  G.projectColor.continuous_of_finiteDimensional.comp (f:=fun u=> G.conjugate u (G.colorMat (x i))) (by unfold Gauge.conjugate; fun_prop)
lemma wheel_away (X:Grove o) {κ K:ℝ}(h:Reliable G κ K)(z:Site c→G.El)(m:ℕ) (V:Config G c): X.crook m Chi.canonical κ (gauge z V)=wheel (z o) (X.crook m Chi.canonical κ V):= by
  funext i; unfold crook; change X.shore m _ i= G.adjoint (z o) (X.shore m _ i)
  rw [shore_apply,shore_apply]; split; next he=> rw [painted]; exact h.conjugate _ _ _
  exact (map_zero _).symm

def castP (P:Pkt E d) (i:Fin d)(u:G.El): Tensor.T E ℝ i:= (P i).compContinuousLinearMap (fun _=> FrameBox.wheel u)
def colorP (P:Pkt E d) : Pkt E d:= fun i=>∫ u:G.El,castP P i u ∂G.probHaar
lemma wheel_clm : Continuous (wheel (G:=G) (c:=c)):= by
  -- via custom joint continuous finite dimensional
  let P:= Module.finBasis ℝ (Directions G c)
  let Z:(E →L[ℝ] E)→ₗ[ℝ] (Fin (Module.finrank ℝ (Directions G c))→ E):= {
    toFun f:=fun i=>f (P i)
    map_add' f g:=rfl
    map_smul' c g:=rfl }
  have hZ:Injective Z:= by
    intro i j h; apply ContinuousLinearMap.coe_injective; exact (P.ext (f₁:=i.toLinearMap) (f₂:=j.toLinearMap) (congr_fun h))
  apply (((Z.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hZ)).choose_spec.2).isInducing Z.continuous_of_finiteDimensional).continuous_iff.mpr -- edit
  exact continuous_pi fun i=> wheel_moves _
lemma cast_cont (P:Pkt E d) (i:Fin d) : Continuous (castP P i):= by
  have hh : Continuous fun u:G.El=>fun _ : Fin i.val=> FrameBox.wheel (c:=c) u := continuous_pi fun _=> wheel_clm
  exact (map_continuous (ContinuousMultilinearMap.compContinuousLinearMapLRight («E»:=fun _ : Fin i.val=> E) (P i))).comp hh
lemma sunwheel (P:Pkt E d)(x:E) : Cabana.actual (colorP P) x= ∫ u:G.El, Cabana.actual P (wheel u x) ∂G.probHaar:= by
  unfold Cabana.actual; simp_rw [Finset.sum_apply]; rw [integral_finsetSum]; swap
  · intro i _; exact ((Tensor.diag_smooth _ ω).continuous.comp (wheel_moves x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply Finset.sum_congr rfl
  intro i _; unfold Tensor.diagonal colorP
  exact -- CLM eval
    ContinuousMultilinearMap.integral_apply (cast_cont P i|>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) _

lemma gauge_p (X:Grove o)(m:ℕ){κ K:ℝ}(h:Reliable G κ K)(P:Pkt (Directions G c) d): GaugeInvariant (FrameBox.realise X m κ (colorP P)):= by
  intro z U; unfold realise; rw [wheel_away X h,sunwheel,sunwheel]; simp_rw [← wheel_prod]; exact integral_mul_right_eq_self (μ:=G.probHaar) (fun u=> Cabana.actual P (wheel u (X.crook m Chi.canonical κ U))) _
lemma legal (X:Grove o)(m:ℕ){κ K:ℝ}(h:Reliable G κ K)(P:Pkt (Directions G c) d)(B:BudgetPoint): B.Regular (neighbors m o) (realise X m κ (colorP P)):=by
  let f:= colorP P; let C:= FrameBox.realise X m κ f
  let W:= (X.crook (G:=G) m Chi.canonical κ)
  have ht (U:Config G c): Local.Chart B.order C U:= by
    change ContDiffAt ℝ _ (Cabana.actual f ∘ (W ∘ increment U)) 0
    apply ((Cabana.moves _ _).contDiffAt.comp 0 ?_)
    refine ((X.shore m).contDiff.contDiffAt.comp 0 ?_)
    let D i x:= G.mat (X.fix (increment U x) i); have hg i: ContDiffAt ℝ ∞ (D i) 0 := by
      have hL i:ContDiffAt ℝ ∞ (fun x=> G.mat (increment U x i)) 0:= (by unfold increment; simp only [G.mat_mul]; exact (((G.exp_jet.comp (contDiff_apply ..)|>.contDiffAt).of_le (by exact le_top)).mul contDiffAt_const))
      have hh (l:Walk) (k:Site c): ContDiffAt ℝ ∞ (fun y=> G.mat (travel (increment U y) k l)) 0:= by
        induction l generalizing k with
        | nil=> simp only [travel]; exact contDiffAt_const
        | cons i l ih=>
          simp only [travel,G.mat_mul]; apply ContDiffAt.mul ?_ (ih _); rcases i with ⟨_,b|b⟩
          · exact hL _
          exact (starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (hL _)
      unfold D Grove.fix Lattice.gauge; simp only [G.mat_mul,G.mat_inv]; exact ((hh _ _).mul (hL _)).mul ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (hh _ _))
    exact contDiffAt_pi.mpr (fun i=> (h.smooth Chi.canonical (show _ from hg i)).of_le (show (B.order : WithTop ℕ∞) ≤ (∞:WithTop ℕ∞) from (show (↑(B.order:ℕ∞):WithTop ℕ∞)≤ ↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)))
  refine ⟨fun x y h=>congr_arg (Cabana.actual f) (X.lark _ _ h ..), ((Cabana.moves f (⊤:WithTop ℕ∞)).continuous.measurable).comp (show Measurable W from ?_), gauge_p X m h P, fun U _=> ht U,fun U _ A l hl=> Next.Foundations.left_has A hl (ht U)⟩
  refine (X.shore m|>.continuous.measurable).comp (measurable_pi_lambda _ (fun i=> ?_)); exact (h.borel _).comp (show Continuous (fun U:Config G c=> X.fix U i) by unfold Grove.fix Grove.uplink Lattice.gauge; fun_prop).measurable
end YM.LocalLTE.FrameBox
