import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Rooms
import YM.RG01Estimate.Parchment
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term
/-!
 # Same aux push, PaneVirgin times rendered polynomial. True flags.
 K set to zero before this estimate on auxiliary (needs Crew from E6).
 Exact finite/infinite E collection and one assertion about model evaluation,
 with no claims on canonical lift or its announced coefficients.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.LayoutWeight
open Function Filter Set Metric Finset Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Animals PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series Boulevard Blaze.Frond Exterior
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Laplace.Layout
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}(T:Tube G S)(F:Forest S.ratio)(B:BudgetPoint)
      (k:S.Choices)(r:Bid.Dir G c→AxisChart G F)(O:ChartRatio G)(t:ℝ)
local notation "X" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
variable {n j i:ℕ} {D s a h β u v Y' D' M N:ℝ} {U: RG.Rep G f} (x : Positions (Uniform.Primary c G))
local notation "b" => gStep β

-- K support arbitrary, evaluating Ψ gas: only no flags density of Virgin. Exact.
variable (hZ : U.p=B) (hC : ∀ i Z,U.activities.K i Z=0)
    (hX : U.path=T.up) (hB : U.beta=β) (hν: U.v=0) (hc:U.clip=T.high)
-- typo U.v

lemma noneK (R:RG.Rep G f) (hC:∀ i Z,R.activities.K i Z=0) (V:Config G f) (h:flags R.p.threshold V≠∅): R.eval V=0:= by
   suffices he : R.activities.gas R.p V=0 by rw [Rep.eval,he,mul_zero]
   have hK i:R.activities.gasOccurrence R.p i V=0:= by
       unfold Activities.gasOccurrence; split; next ht=>
          have h': (i:Finset ℕ).Nonempty:= Finset.nonempty_iff_ne_empty.mpr (fun hx=> h (by have h:= ht.2; simp only [hx] at h; exact h.symm))
          obtain ⟨j,hj⟩:=h'; exact Finset.prod_eq_zero hj (hC _ V)
       rfl
   simp [Activities.gas,hK]

include hZ hC hX hB hν hc
lemma retained (V : Config G f): U.eval V = (Pane.virgin T B β).eval V * Real.exp (-Boulevard.throng U.activities.E V) := by
    by_cases h:flags B.threshold V=∅
    · rw [Rep.eval,Rep.exponent, hν,hX,hZ,hB,hc,Pane.crystalline _ _ _ _ _ h,Activities.gas_one _ _ h,mul_one,Pane.sparkling,if_pos h,← Real.exp_add]; have hv : U.activities.additive B V=Boulevard.throng U.activities.E V:= tsum_congr fun i=> masked_eq _ _ _ _ (by unfold Healthy; rw [h]; simp); rw [hv,zero_mul,zero_sub, sub_eq_add_neg]
    rw [noneK U hC V (hZ ▸ h), Pane.sparkling, if_neg h, zero_mul]

section powers
variable {P : Teller G} (p:Intake P T t (Pane.virgin T B β))
variable (u':Poll.Body (Precision.Key F G)→ℝ × Positions (Uniform.Primary c G)→ℝ) (a' : ℝ)
-- Producer sends log L smooth atlas. For other circumstances send verified complete weights.
variable (hq:Roll u' (closedBall 0 D) (ball 0 Y') (breath G S.patch.L t) h j)
    (hα : Atlas u' (ball 0 Y') i j u)
    (hw : ∀ z:Poll.Body (Precision.Key F G),∀ y∈ ball 0 Y',u' z (0,y)=0)
    (hh:h*breath G S.patch.L t≤1)(hp:1 ≤ j)
    (hδ: ∀ x∈ Set.Icc (-1:ℝ) 1,Brush j a' 1 Real.exp x)(ha:0≤ u)(hm:0≤ a')
    -- norm & gauge
    (hA:StronglyMeasurable U.eval)(hG:GaugeInvariant U.eval)(hr : ∀ V:Config G f,flags B.threshold V=∅ → ‖Boulevard.throng U.activities.E V‖ ≤ s)
    (hR:∀ y ∈ closedBall (gStep β • x) (furl G S.patch.L t),∀ z:Poll.Body (Precision.Key F G), ‖z‖≤D →
        -(Boulevard.throng U.activities.E (field F r β y z))= u' z (gStep β,(gStep β)⁻¹ • y))
    (hK: Real.exp s≤ v)
include hX hC hq hα hw hh hp hδ ha hm hA hG hr hR hK hν
lemma fruits : Receipt.Article T F B r t (clump j h a') D Y' β v (clump j u a') x U.eval (fun z=>Real.exp ∘ u' z) (i*j+0) j:= by
   have hf:=retained T B hZ hC hX hB hν hc
   refine ⟨hA,hG,?_,fun i=>?_,Layout.vac_small u' measurableSet_closedBall hq (fun i _=>hw i) hh hp hδ, Layout.vac_atlas u' hα hw hp ha hm hδ,fun y hy z hz=>?_⟩
   · unfold clump; positivity
   · rw [hf]; by_cases h:flags B.threshold i=∅
     · rw [Pane.sparkling,if_pos h,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (Real.exp_pos _).le,mul_comm]
       apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; apply le_trans (Real.exp_monotone ?_) hK
       exact (neg_le_abs _).trans (hr _ h)
     rw [Pane.sparkling,if_neg h,zero_mul,mul_zero,norm_zero]
   dsimp only; rw [hf,hR y hy z hz]; rfl
omit hR hr hA hG hK
-- Lawfulness of THESE unmarked extras is a real input hypothesis.
lemma affairs {d δ k f':ℝ}
    (ht:U.Lawful d k f' s δ)
    (hS:∀ y∈ closedBall (gStep β • x) (furl G S.patch.L t),∀ z:Poll.Body (Precision.Key F G), ‖z‖≤D→
        -(U.activities.additive B (field F r β y z))= u' z (gStep β,(gStep β)⁻¹ • y))
    (hΨ:∀ y∈ closedBall (gStep β • x) (furl G S.patch.L t),∀ z:Poll.Body (Precision.Key F G), ‖z‖≤D→
        flags B.threshold (field F r β y z)=∅) (hK:Real.exp (Fintype.card (Site f)*s)≤ v):
     Receipt.Article T F B r t (clump j h a') D Y' β v (clump j u a') x U.eval (fun z=>Real.exp ∘ u' z) (i*j+0) j:= by
   have hc' := ht.labels.boundE
   apply fruits T F B r t x hZ hC hX hB hν hc u' a' hq hα hw hh hp hδ ha hm
     (U.envelope ht|>.meas.stronglyMeasurable) (Presented.lawful_gi ht) _ _ hK
   swap
   · intro y hy z hz
     rw [← hS y hy z hz]; apply congr_arg Neg.neg
     refine tsum_congr (fun i=>Eq.symm (masked_eq _ _ _ _ ?_)); unfold Healthy; rw [hΨ y hy z hz]; simp
   intro V hV
   obtain ⟨A,hA,hq⟩:= hc'; let E:=U.activities.E; let R:= U.activities.reg
   have he:=budget_over Finset.univ _ (fun _=> s) (fun i _=>hq i)
   have hh i : ‖E i V‖ ≤ A i := (hA i).2 V (by unfold Healthy; rw [hZ,hV]; simp) [] (Nat.zero_le _) (by simp)
   have hz := budget_mono he (g:=fun i=> ‖E i V‖) (fun i=> norm_nonneg _) (fun i=>?_)
   · unfold Boulevard.throng; refine (norm_tsum_le_tsum_norm hz.2.1).trans ?_; exact hz.2.2.trans_eq (by simp)
   simp only [sum_ite_eq,Finset.mem_univ, if_true]; exact (hh i).trans (U.p.loMass _ _ (hA i).1)
end powers
end YM.RG01Estimate.LayoutWeight
