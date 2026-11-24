import YM.RGComparison01.AuxDesk
/-!
# Perturbed true kernel (analytic vacuum sector, E-test/marker part)

Estimate complement of stationary domain of auxiliary chart with real likelihood.
Includes changing domains when V moves. Won't differentiate truncated domains to get
any true-kernel estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxWeigh
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {L : Side} {P : Teller G} {C Z u a p c' σ η W : ℝ}
  {f c : Side} {S:StepData c f}
variable (F: Forest S.ratio) (T : Tube G S) (A:ChartRatio G) (ρ : Bid.Dir G c→AxisChart G F)
  (B : BudgetPoint) (k:S.Choices) (β:ℝ)
local notation "M₀" => Lapis.gram F T.up T.high ρ k
local notation "U₀" => Lapis.table F k T.up T.high
local notation "M" => Pane.virgin T B β
local notation "δ" => gStep β
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun x:Xs=> represent (tint G _ x))
local notation "µ" => sweep (M₀ 0)⁻¹
local notation "r" => Lapis.orbit F ρ
local notation "U₁" => overall F T B β
variable (J : Config G f → ℝ) {t : ℝ} (p' : Intake P T t (Pane.virgin T B β))
def weighed (x:Xs) := S.push β ((Pane.virgin T B β).eval * J) (V x)
def assay (x:Xs):= solar F A β * Real.exp (-coverLog F T A k ρ β x)
def rescale := weighed T B β J / assay F T A ρ k β
include p'
lemma stipend (p : GaugeInvariant J) (hr : RG.Envelope J) (x:Xs):
    RG.Envelope (fun i:F.Slice G=> (U₁ (V x) i)*J (F.drape i)) ∧ weighed T B β J x=∫ i,(U₁ (V x) i)*J (F.drape i) ∂F.order G := by
  have ha : S.patch.Branches S.kernel G:= p'.ready.knobs.symm ▸ p'.ready.kernel
  have ht: GaugeInvariant (M).eval:= lawful_gi p'.cap
  have he: GaugeInvariant ((M).eval * J) := fun g U=> by simp only [Pi.mul_apply, ht g U,p g U]
  have hH:= (M).envelope p'.cap; have hu:= amt F T B β _ P p' (V x)
  refine ⟨hu.1.mul (Env.along hr F.continuous_drape.measurable),?_⟩
  unfold weighed; rw [F.pushing (S.isKernel ha β) _ (V x) he ((hH.mul hr).integrable _) (fun k U=>S.covary ha k β U (V x))]; apply integral_congr_ae; filter_upwards with a; rw [Fare.total]; exact (mul_assoc ..).symm
local notation "W'" => AuxGrace.nodes U₀ (mist F A T.up) r M₀
section receipt
variable {j : ℕ} {x : Positions (Uniform.Primary c G)} {D v C v' : ℝ} {T₀:ℝ}
  (hP : KeysReady T B F ρ k A D β x) (hv: GaugeInvariant J) (hJ: Envelope J)
  (hH : ∀ i:Config G f, flags B.threshold i=∅ → |J i| ≤ T₀) (hT : 0 ≤ T₀)
  (he : LocalRatio A) (hβ : 0<β)
  (hk : Golf (Lapis.table F k T.up T.high) (Lapis.mist F A T.up) (Lapis.orbit F ρ)
    (Lapis.gram F T.up T.high ρ k) j D v v C)
  (hh : gStep β < v) (hx : ‖x‖ < v)
local notation "P'" => assay F T A ρ k β x
local notation "D₀" => closedBall (0:Y) D
local notation "Ω" => staying F (r x) δ D (V x)
include hv hJ hH hT he hβ hk hP hh hx
lemma credit (Z:Y→ℝ×Xs→ℝ) (hE: ∀ z∈D₀,W' z (δ,x)* J (F.drape (draw F (V x) (r x+δ • z)))=Z z (δ,x))
    (hr : tramp T B β x- P'*ratify U₀ (mist F A T.up) r M₀ D (δ,x)≤ P'*v') :
    ‖rescale F T A ρ B k β J x-intake (M₀ 0)⁻¹ Z D (δ,x)‖ ≤ T₀*v':= by
  let g (i:F.Slice G):= U₁ (V x) i * J (F.drape i)
  have hp : 0<P':= mul_pos (Fare.sun _ _ _ hβ he) (Real.exp_pos _)
  have ha : S.patch.Branches S.kernel G:= p'.ready.knobs.symm ▸ p'.ready.kernel
  obtain ⟨h',hy,hL⟩:=hP; have hz := (Fare.gS _ hβ).1
  have ht := amt F T B β _ P p' (V x); have hc:= pricing F T A k ρ B β _ hk hβ hh ha hx h' he hy hL (ht.1.meas.stronglyMeasurable)
  let X:=F.order G
  have hb : ∫ y in Ωᶜ, U₁ (V x) y ∂X ≤ P'*v':= by
    have h₀:= integral_add_compl (s:=Ω) (staying_meas ..) (ht.1.integrable X)
    rw [hc, ← ht.2] at h₀
    exact (eq_sub_of_add_eq' h₀).trans_le hr
  obtain ⟨hq,hv⟩:= stipend F T B β J p' hv hJ x
  have hg : ∫ y in Ω, g y ∂X=P' * intake (M₀ 0)⁻¹ Z D (δ,x):= by
    rw [cubits F A _ _ _ _ _ hz he hy hq.meas.stronglyMeasurable,← integral_const_mul]; unfold intake; rw [Blaze.Shield.recommends _ (hk.gram 0 (by rw [norm_zero]; exact hk.pos)).1.inv]
    rw [← integral_const_mul, ← integral_indicator measurableSet_closedBall]; apply integral_congr_ae; filter_upwards with z
    by_cases H:z∈D₀; swap
    · unfold AuxConstant.truncate; rw [indicator_of_notMem H,indicator_of_notMem H]; ring
    unfold AuxConstant.truncate; rw [indicator_of_mem H,indicator_of_mem H, ← hE z H]; let y':=J (F.drape (draw F (V x) (r x+δ • z)))
    have hp':= reserves F T A k ρ B β D hk hβ hh ha hx h' he hy hL z H
    let m:= Fintype.card (Precision.Key F G); let p:= pay A (windmill F (r x+δ • z))
    change δ^m * (p *( U₁ (V x) (draw F (V x) (r x+δ • z))*y'))= P' * ( _ * (W' z (δ,x)*y')); rw [←mul_assoc p,← mul_assoc, hp']; simp only [mul_assoc,assay,AuxGrace.nodes,Function.comp_apply]
  let e:= ∫ y in Ωᶜ,g y ∂X
  have hμ : ‖e‖ ≤ T₀*(P'*v'):= by
    refine (norm_integral_le_integral_norm _).trans ((integral_mono (μ:=X.restrict Ωᶜ) (hq.integrable X).norm.integrableOn (((ht.1.integrable X).const_mul T₀).integrableOn) (f:=fun i=> ‖g i‖) (fun i=>?_)).trans ?_)
    · dsimp only; unfold g; rw [norm_mul,Real.norm_of_nonneg (rays F T B β i x),mul_comm T₀]
      by_cases hi: flags B.threshold (F.drape i)=∅; exact mul_le_mul_of_nonneg_left (hH _ hi) (rays ..)
      rw [Fare.total,Pane.sparkling,if_neg hi,mul_zero,zero_mul, zero_mul]
    rw [MeasureTheory.integral_const_mul]; exact mul_le_mul_of_nonneg_left hb hT
  have hW : weighed T B β J x= P'*intake (M₀ 0)⁻¹ Z D (δ,x) + e:= by rw [← hg,hv]; exact (integral_add_compl (staying_meas ..) (f:=g) (hq.integrable X)).symm
  rw [rescale,Pi.div_apply,hW,add_div,mul_div_cancel_left₀ _ hp.ne',add_sub_cancel_left, norm_div,Real.norm_of_nonneg hp.le]
  apply (div_le_iff₀ hp).mpr; exact hμ.trans_eq (by ring)
end receipt
end YM.RGComparison01.AuxWeigh
