import YM.Juniper.LocalAtlas.Reroot
/-!
 # One transmission core comparator family

 Coupling variable **and all external directions** at once. Compare full
 polynomial projected from UNcut Poll, not from the numerical Ratify disk
 (width choices, Bolt, receipts stay in error side). This is before
 comparing tree choices, taking normalized ratio, resetting, etc. Keep the
 one integrand & reference of this authentic Wilson projector family; don't
 transport β through derivative estimates. `Tensor` is a real continuous
 **multilinear map**. Price its operator norm (needed before Box lift).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open MeasureTheory Set Function Matrix Metric Filter ProbabilityTheory
open PhysicalNext.Repeat Lantern
open ConnectedActivityE6 Blaze Brush Poll
open Work.G05 WilsonStartup Analysis Tensor
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {ι : Type}[Fintype ι][DecidableEq ι]
    {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {φ ψ : E × Poll.Body ι→ℝ}{ρ:E→ Poll.Body ι}{M : E→ Matrix ι ι ℝ}
    {k : ℕ}{D b p W q : ℝ}
local notation "V" => ℝ × E
local notation "E#" => Poll.Body ι
local notation "g" => grace φ ψ ρ M
local notation "K!"=> (M 0)⁻¹
local notation "μ" => sweep (M 0)⁻¹
local notation "v" => Lantern.vote φ ρ

variable (H : Golf φ ψ ρ M k D b b p) (hD:1 ≤ D)
include H hD

lemma outskirts (q:ℝ)(hq:1 ≤ q) {x:ℝ×E}(hx: turn q x∈ cylinder b b E):
    ContinuousOn (fun z=> g z x) (closedBall (0:Poll.Body ι) q) := by
  let y:=turn q x; let X: Set (ℝ×E):=cylinder b b E; let Z:=closedBall (0:Poll.Body ι) D; let Y:=closedBall (0:Poll.Body ι) q
  let w(z: Poll.Body ι):=q⁻¹ • z; have hp:=zero_lt_one.trans_le hq
  have Hw: MapsTo w Y Z:=fun z hz=> by rw [mem_closedBall_zero_iff,norm_smul,Real.norm_of_nonneg (show 0 ≤ q⁻¹ by positivity)]; exact le_trans ((inv_mul_le_iff₀ hp).mpr (show ‖z‖≤ q*1 from (mem_closedBall_zero_iff.mp hz).trans_eq (mul_one q).symm)) hD
  have hv: y∈ ball (0:ℝ) b ×ˢ ball (0:E) b:=hx
  have hG: ContinuousOn (fun z:Poll.Body ι=> grace φ ψ ρ M z y) Z:= Lantern.gallon D H (mem_ball_zero_iff.mp hv.2) (mem_ball_zero_iff.mp hv.1)
  have hy t (ht:t∈ Icc (0:ℝ) 1) : ContinuousOn (fun z:Poll.Body ι=> ψ (visit ρ z t y)) Z:= fun z hz=> (((H.color z t y (mem_closedBall_zero_iff.mp hz) ht (mem_ball_zero_iff.mp hv.1) (mem_ball_zero_iff.mp hv.2)).2.smooth.continuousAt).comp (f:=fun z => visit ρ z t y) (show ContinuousAt (fun z=> visit ρ z t y) z by unfold visit; fun_prop)).continuousWithinAt -- projection
  have h : ContinuousOn (fun z=> vote φ ρ z (0,0)-vote φ ρ z y) Z:= by
    refine ((hG.sub (continuousOn_const (c:=Lantern.shade M y.2-Lantern.shade M 0))).sub ((hy 0 (by simp)).sub (hy 1 (by simp)))).congr ?_
    exact fun z _=> (show v z (0,0)-v z y=g z y-(Lantern.shade M y.2-Lantern.shade M 0)-(ψ (visit ρ z 0 y)- ψ (visit ρ z 1 y)) from by unfold grace; ring) -- placeholders
  have hh := (hG.add ((continuousOn_const (c:=q^2-1)).mul h)).comp (show ContinuousOn w Y from (by unfold w; fun_prop)) Hw
  refine hh.congr (fun z _=>?_)
  change g z x=g (w z) y + (q^2-1)*(v (w z) (0,0)-v (w z) y)
  nth_rw 1 [← show q • w z=z from smul_inv_smul₀ hp.ne' z]; exact branches q (w z) x

-- local with cutoff per comparison scale
lemma cut_meas (q:ℝ)(hq:1 ≤ q) {x:ℝ×E}(hx:turn q x∈cylinder b b E): Measurable (ballots φ ψ ρ M q x) := by
  let s:= closedBall (0:Poll.Body ι) q; let B:= fun z=>Real.exp (g z x)
  apply measurable_of_restrict_of_restrict_compl (s:=s) measurableSet_closedBall
  · rw [show s.restrict (ballots φ ψ ρ M q x)=s.restrict B from funext fun i=> Set.indicator_of_mem i.2 B]
    exact (continuousOn_iff_continuous_restrict.mp (Real.continuous_exp.comp_continuousOn (outskirts H hD q hq hx))).measurable
  rw [show sᶜ.restrict (ballots φ ψ ρ M q x)=(fun _=>0) from funext fun i=> Set.indicator_of_notMem i.2 B]; exact measurable_const

omit H hD [FiniteDimensional ℝ E] in
private lemma indicator_jet (q:ℝ)(z:Poll.Body ι)(i:ℕ) :
    JetF (ballots φ ψ ρ M q) i (0:ℝ×E) z= (closedBall 0 q).indicator (fun z=>iteratedFDeriv ℝ i (Real.exp ∘ g z) 0) z:= by
   by_cases hz:z∈closedBall 0 q
   · rw [indicator_of_mem hz]; exact congr_arg (fun f:ℝ×E→ℝ=>iteratedFDeriv ℝ i f 0) (funext fun i=> Set.indicator_of_mem hz _)
   rw [show JetF (ballots φ ψ ρ M q) i 0 z = iteratedFDeriv ℝ i (0 : ℝ×E→ℝ) 0 from congr_arg (fun f:ℝ×E→ℝ=>iteratedFDeriv ℝ i f 0) (funext fun i=>Set.indicator_of_notMem hz _),iteratedFDeriv_zero,Pi.zero_apply,Set.indicator_of_notMem hz]

set_option maxHeartbeats 200000 in
lemma transport_meas (i:ℕ)(hi:i ≤ k): AEStronglyMeasurable (fun z => iteratedFDeriv ℝ i (Real.exp ∘ g z) (0:ℝ×E)) μ := by
  let f := fun z => iteratedFDeriv ℝ i (Real.exp ∘ g z) (0:ℝ×E)
  let s (q:ℕ):= closedBall (0:Poll.Body ι) (q+1 : ℝ)
  have hx : (μ).restrict (⋃ q:ℕ,s q)= μ:= by
    have he : (⋃ q:ℕ,s q)=Set.univ := eq_univ_of_forall fun x=> by
      obtain ⟨n,h⟩:= exists_nat_gt ‖x‖; exact Set.mem_iUnion.mpr ⟨n,mem_closedBall_zero_iff.mpr (by linarith : ‖x‖ ≤ (n:ℝ)+1)⟩
    rw [he,Measure.restrict_univ]
  rw [← hx]; apply aestronglyMeasurable_iUnion_iff.mpr; intro n; let q:= (n:ℝ)+1
  have he:1 ≤ q:= by unfold q; simp
  let F(z) (x):= ballots φ ψ ρ M q x z
  let Z:= (turn (E:=E) q)⁻¹' cylinder b b E
  have h0: (0:ℝ×E) ∈ Z := by rw [mem_preimage,map_zero]; exact ⟨mem_ball_self H.pos,mem_ball_self H.pos⟩
  have ht : StronglyMeasurable fun z=>iteratedFDeriv ℝ i (F z) (0:ℝ × E) := by
    refine Meristem.legs (j:=k) (S:=Z) ((isOpen_ball.prod (isOpen_ball)).preimage (turn q).continuous) (fun z x hx=> ?_) (fun x hx=> (cut_meas H hD q he hx).stronglyMeasurable) hi h0 -- arg case S= uppercase?
    by_cases hy:z ∈ s n
    · refine ((abroad H hD q he x hx z (mem_closedBall_zero_iff.mp hy)).smooth.exp).congr_of_eventuallyEq (Eventually.of_forall fun x=>Set.indicator_of_mem hy _)
    exact contDiffAt_const.congr_of_eventuallyEq (Eventually.of_forall fun _=> Set.indicator_of_notMem hy _)
  exact (aestronglyMeasurable_indicator_iff («μ»:=μ) (s:=s n) (f:=f) measurableSet_closedBall).mp (((show (fun z=>iteratedFDeriv ℝ i (F z) (0:ℝ×E))=(s n).indicator f from funext fun z=> indicator_jet q z i)) ▸ ht.aestronglyMeasurable)

-- factorial convention included! Exponential power series normalized by true relative
-- Haar and Gaussian central shift. root E uses *rescaled* arguments in BOTH Γ and stationary.
section
variable (φ ψ : E × Poll.Body ι→ℝ)(ρ:E→ Poll.Body ι)(M : E→ Matrix ι ι ℝ)
def coin (i:ℕ)(z):= Tensor.coeff (Real.exp ∘ grace φ ψ ρ M z) i 0
def oneEra : PacketSeries (ℝ×E) ℝ := fun i=> ∫ z, coin φ ψ ρ M i z ∂(sweep (M 0)⁻¹)
end

variable {c:ℝ} (hc : ∀ z:ι→ℝ, dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ c * dotProduct z z)
variable (hW : ∀ y∈Set.Icc (-1:ℝ) 1, Brush k W 1 Real.exp y)
local notation "c!" => oneEra φ ψ ρ M
local notation "t!"=> (k+2)*k
local notation "p!"=> preAux k p D W
local notation "y!"=> coin φ ψ ρ M
include hW
lemma pre_nn : 0 ≤ preAux k p D W := by unfold preAux clump; have h:= (hW 0 (by simp)).nonneg; have hz:=fee_nn H hD; positivity
lemma full_bill (i:ℕ) (hi:i≤ k)(z:E#): ‖y! i z‖≤ p!*bill ((k+2)*k) z:=by
  let u:= (1:ℝ)+‖z‖
  have he := height H hD z (le_add_of_nonneg_right (norm_nonneg z)) (show ‖z‖ ≤ u from le_add_of_nonneg_left zero_le_one)
    (x:=(0,0)) (by rw [show turn u (0,(0:E))=(0,0) from map_zero _]; exact ⟨mem_ball_self H.pos,mem_ball_self H.pos⟩) (hW _ (by rw [zeroC]; simp))
  exact capped he i hi
include hc
lemma coin_limit (i:ℕ) (hi:i ≤ k) {A:ℝ} (hA:(Fintype.card ι:ℝ) ≤ A) :
    Integrable (y! i) μ ∧ ‖c! i‖ ≤ p!*gamut A c ((k+2)*k) := by
  have h0: ‖(0:E)‖< b:=by rw [norm_zero]; exact H.pos
  have hv:=(H.gram _ h0).1.inv
  have hs:=moment hv hc hA ((k+2)*k)
  have he : AEStronglyMeasurable (y! i) μ:= (transport_meas H hD i hi).const_smul (_:ℝ)
  have hi' := (hs.1.const_mul (p!)).mono' he (Eventually.of_forall (full_bill H hD hW i hi))
  refine ⟨hi', (norm_integral_le_of_norm_le ?_ (?_ : ∀ᵐ z∂μ, ‖y! i z‖≤ (p!)*bill ((k+2)*k) z)).trans ?_⟩
  · exact hs.1.const_mul (p!)
  · exact Eventually.of_forall (full_bill H hD hW i hi)
  rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hs.2 (pre_nn H hD hW)

lemma debt (i:ℕ)(hi:i ≤ k){A ε a:ℝ}(hA:(Fintype.card ι:ℝ) ≤ A)(he:0<ε)(ht : (μ).real (closedBall (0:Poll.Body ι) D)ᶜ ≤ a):
    ‖oneEra φ ψ ρ M i- ∫ z in (closedBall (0:Poll.Body ι) D),y! i z ∂ μ‖ ≤ p! * (ε*gamut A c (2*t!)+ a*ε⁻¹):= by
  have hg := (H.gram _ (show ‖(0:E)‖<b by rw [norm_zero]; exact H.pos)).1.inv
  unfold oneEra; rw [← integral_add_compl (s:= closedBall (0:Poll.Body ι) D) measurableSet_closedBall ((coin_limit H hD hc hW i hi hA).1),add_sub_cancel_left]
  have hh:= moment hg hc hA t!
  refine (norm_integral_le_of_norm_le («g»:=fun z=>p!*bill t! z) ((hh.1.const_mul (p!)).integrableOn) (Eventually.of_forall (full_bill H hD hW i hi))).trans ?_
  rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (outside hg hc hA t! _ (measurableSet_closedBall.compl) ht he) (pre_nn H hD hW)
omit hc
include H hW
lemma cuttable (ha : fee k p D*b ≤ 1)(hk : 1 ≤ k)(i:ℕ)(hi:i ≤ k): Tensor.coeff (ratify φ ψ ρ M D) i 0 = ∫ z in (closedBall (0:Poll.Body ι) D), y! i z ∂ μ:= by
  -- from Predict.burs core but need integrability and calibration
  let B:= ballots φ ψ ρ M D; let Y := cylinder b b E
  let f:= ratify φ ψ ρ M D; let s:= closedBall (0:E#) D; have h0: (0:ℝ×E)∈ cylinder b b E:= ⟨mem_ball_self H.pos, mem_ball_self H.pos⟩
  have he: ∀ᶠ x in 𝓝 (0:ℝ×E), x∈Y:= (isOpen_ball.prod (isOpen_ball)).mem_nhds h0
  let C:=clump k (fee k p D) W
  have hx(y:ℝ×E)(hy:y∈Y)(z):Brush k C 1 (fun y=> B y z) y:=by
    by_cases H':z∈s; swap
    · apply ((Brush.certified (x:=y) (k:=k) zero_le_one (0:ℝ)).shimmy (Eventually.of_forall fun x=> Set.indicator_of_notMem H' _)).climb _ le_rfl
      have he:0 ≤ fee k p D:= (compel D H (mem_ball_zero_iff.mp hy.2) (mem_ball_zero_iff.mp hy.1) (z:=0) (by rw [norm_zero]; exact zero_le_one.trans hD)).nonneg
      have hv:= (hW 0 (by simp)).nonneg; unfold C clump; rw [norm_zero]; positivity
    have ht := mem_closedBall_zero_iff.mp H'
    exact (composite (compel D H (mem_ball_zero_iff.mp hy.2) (mem_ball_zero_iff.mp hy.1) ht)
      (hW (g z y) (ether D H (mem_ball_zero_iff.mp hy.2) (mem_ball_zero_iff.mp hy.1) hk (by rw [max_self]; exact ha) z ht))).shimmy (Eventually.of_forall fun x=>Set.indicator_of_mem H' _)
  have hm: Meristem B 0 μ k := (Meristem.points B μ ⟨fun _=> C,integrable_const _, he.mono hx⟩ (he.mono fun x h=> duties D H (mem_ball_zero_iff.mp h.2) (mem_ball_zero_iff.mp h.1))).1 -- he .mono mem? adjust
  unfold Tensor.coeff; rw [show iteratedFDeriv ℝ i (ratify φ ψ ρ M D) 0 = _ from (hm.calls|>.2 i hi).2, ← integral_smul]; symm
  rw [← integral_indicator measurableSet_closedBall]
  unfold B; simp_rw [indicator_jet]; refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hy:z∈closedBall (0:Poll.Body ι) D
  · rw [Set.indicator_of_mem hy,Set.indicator_of_mem hy]; rfl
  rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem hy,smul_zero]

end YM.Juniper.LocalAtlas
