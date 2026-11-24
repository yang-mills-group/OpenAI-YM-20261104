import YM.LocalLTE.FieldPT.Hero
/-! Powers-to-actual estimate per coefficient. -/
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
variable {G : Gauge} {n L : Side} {j z k m i:ℕ} {W κ K U C V t H u v: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
open Scene
variable {a:RegularAddress n}(X:Art a z)(p:BudgetPoint)(f:ℝ→Pot G n)(s:ℝ)
-- field payouts for arbitrary V.In. Frame.Content B. Budget dimensions. Burn Forecast no ω order; derivative disks.
local notation "E"=> Directions G n
lemma magnify (G:Gauge) (L:Side) {T:ℝ→ℕ} (hf:Rate G L 0 fun x=>(T x:ℝ))(hp:Reliable G κ K)(he:-(1/2:ℝ)<v)(ht:v< u)(hv:u<0)(hz:v < Sienna.vow)(g e j:ℕ) : ∃ B:ℝ→ℝ, Rate G L (u*j) B ∧∀ᶠ x in atTop,∀ (n:Side)(P: BudgetPoint),P.threshold=Pressure.temp x → P.threshold≤ 2*Pressure.fiery G x L → P.order=g →P.power=e → ∀ (z:ℕ)(a:RegularAddress n)(A: Price.Art a z),z≤ T x → 32*z<n.val→ ∀ u: Tensor.T (Directions G n) ℝ j,P.supBounds a.site a.support (play A κ u) (‖u‖* |B x|) :=by
     obtain ⟨B,hB,H⟩:= FrameBox.minted G L hf hp ht hv he hz g e
     let p x:= YM.LocalLTE.Inset.cone u (betaF G x L)
     let C x:= B x * (p x)^j * ((1+(j:ℝ))^g); have hC : Rate G L (u*j) C:=by simpa only [zero_add] using! ((hB.mul ((Rate.power (G:=G) (L:=L) (a:=u)).pow j)).mul_right ((1+(j:ℝ))^g))
     refine ⟨C,hC,?_⟩
     filter_upwards [H,Delay.shift_pos G L] with t ht hv n P hP hQ hT hp' z a A ha hy U
     let X:= A.grove; let l:= A.radius; have hz: l< z:= A.bonus
     let Q:Cabana.Pkt (Directions G n) (j+1):= Pi.single (M:=fun j:Fin (j+1)=>Tensor.T (Directions G n) ℝ j) (Fin.last j) U
     let q:= p t; have hq:0<q:=Real.rpow_pos_of_pos hv _
     have hx: Cabana.actual Q = Tensor.diagonal U:= by
         funext x; unfold Cabana.actual; rw [Finset.sum_apply,Finset.sum_eq_single (Fin.last j)]; swap
         · intro i hi hu; have hp:Q i=0:=Pi.single_eq_of_ne hu _; rw [hp]; rfl
         · unfold Q; simp
         simp
     let K':= ‖U‖*q^j*(1+(j:ℝ))^g; have h':0≤ K':=by unfold K'; positivity
     have hA:= ht l z ha hz P hp' hT hP hQ n a.site (by omega) (by omega) X _ Q 0 K' h' (reg_const _) (?_)
     · rw [A.crisp]; apply VerifiedReset.sup_le ?_ (mul_le_mul_of_nonneg_left (le_abs_self (C t)) (norm_nonneg U))
       have hg:= AnalyticBridge.CouplingShape.sup_scale (-1) hA; rw [zero_sub,neg_one_smul,abs_neg,abs_one,one_mul,neg_neg] at hg; rw [show B t*K'= ‖U‖ * C t from (by unfold C K' q; ring)] at hg; exact hg
     intro x hx' hr; rw [hx]; let Ld:=ContinuousLinearMap.id ℝ (Directions G n); have he:Brush g q q⁻¹ Ld x := Brush.linearB _ (show ‖x‖ ≤ p t from hx'.le) (by rw [mul_inv_cancel₀ hq.ne']; exact ContinuousLinearMap.norm_id_le) (inv_nonneg.mpr hq.le); have hp:= (LocalLTE.Weft.Arp.stemB he j U).opposite
     simp only [Pi.zero_apply,zero_sub]; refine ⟨hp.smooth,inv_nonneg.mpr hq.le,fun i hi=> (hp.order i hi).trans (?_)⟩; rw [mul_pow]; unfold K'; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (Nat.cast_nonneg j) (le_add_of_nonneg_left zero_le_one) i).trans (pow_le_pow_right₀ (by simp) hi)) (by positivity)) (by positivity)
lemma hatCost (G:Gauge)(L:Side)(i:J k) : ∃ B:ℝ→ℝ, Rate G L (((k:ℝ)-(i.val:ℝ))/2) B∧∀ᶠ x in atTop,∀ b:ℝ, (betaF G x L)/2 ≤ b→ b≤ 2*betaF G x L → |Weft.mark k i (gStep b)| ≤ B x:=by
   let f x:=2*gStep (betaF G x L); let h x:= Real.sqrt (2*betaF G x L)
   have hh:Rate G L (1/2) h:=by
       apply (Rate.mul_left (Rate.power (G:=G) (L:=L) (a:=1/2)) (Real.sqrt 2)).compare; filter_upwards with i; exact le_of_eq (congr_arg abs (Real.sqrt_mul (by norm_num) _ |>.trans (by rw [Real.sqrt_eq_rpow (betaF ..)]))) -- edit
   refine ⟨fun x=> (f x)^i.val*(h x)^k, ((Sienna.glim G L|>.pow i.val).mul (hh.pow k)).weaken (by linarith),?_⟩
   filter_upwards [Delay.shift_pos G L] with t he b hl hm; have hv := Sienna.lamp G L he b hl; have hb:(gStep b)⁻¹ ≤ h t:=by unfold gStep h; rw [inv_inv]; exact Real.sqrt_le_sqrt hm
   unfold Weft.mark; rw [abs_of_nonneg (div_nonneg (pow_pos hv.1 _).le (pow_pos hv.1 _).le),div_eq_mul_inv,← inv_pow]; exact mul_le_mul (pow_le_pow_left₀ hv.1.le hv.2 _) (pow_le_pow_left₀ (inv_nonneg.mpr hv.1.le) hb _) (pow_nonneg (inv_nonneg.mpr hv.1.le) _) (pow_nonneg (hv.1.le.trans hv.2) _)
end YM.AnalyticBridge.VerifiedReset.Collection.Price
