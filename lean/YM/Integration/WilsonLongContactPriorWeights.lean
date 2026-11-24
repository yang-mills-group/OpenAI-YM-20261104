import YM.Integration.WilsonLongContactPriorBallot
/-! The genuine singleton in each marked finite ticket, with its complete former source. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactPriorWeights
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt Brim Next.Foundations AnalyticBridge.LocalGaussianLaws
open YM.Integration.WilsonLongContactTown WilsonLongContactFrozenGaussian
open scoped Topology Classical BigOperators

open RG.Shoot Marker Overlay RG3.Held RG3.Forms RG3.Script.Picnic Push.AbsoluteSums LocalComparison
open Progress.DirectedRecipe MergeProof MergeProof.Menu ManuscriptQLocalMarkedRoster
open ManuscriptQLocalMarkedLeaves ManuscriptQLocalMarkedOffers
open Merge Merge.Palette PhysicalNext.Repeat.WilsonLongContactUnaryAverage RGLocalTaylor
variable {G : Gauge} {c f L : Side} {S : StepData c f} {Y : Rep G f} {T₀ : Tube G S}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W x μ α : ℝ} {o : Target.Order G W}
    {X V : Type} [Fintype V] [DecidableEq V] {Γ : Census V} {seats : V → Site f}
    {T : Taste X seats Y Γ} {w : V → ℝ} {κ a b : ℝ} (B : FullBudget Y.p T w κ a b)
    (H : Cash W x μ L Q o α T₀ (QLocalInheritedRegularSlots.carrier Y))
    (base y : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ))

theorem rooted (D:Finset ((Occurrence E (live (T:=T) K))×Bool)) (root:Site f) (δ:ℝ) (hp:0≤δ)
    (field:(Occurrence E (live (T:=T) K))×Bool→ℝ):
    let u:=(ManuscriptQLocalMarkedRoster.promised B base y E K).terms
    (∀ i∈D,root∈(u i).M.crest→|field i|≤δ*Y.p.mass (u i).M.crest (u i).M.weight) →
    (∑i∈D, if root∈(u i).M.crest then Menu.sumFee (u i) w * |field i| else 0) ≤
      δ*(2*((Fintype.card V:ℝ)*a+(Fintype.card V:ℝ)*(κ*b))):=by
  intro u bills
  have paid:=Extra.Multi.Budget.cap ((ManuscriptQLocalMarkedRoster.offer B base y E K).budget root) D
  calc
    _ ≤ ∑i∈D,δ*(if root∈(u i).M.crest then Menu.fare (u i) w*
      Real.exp (Y.p.supportExponent*coverNumber Y.p.B (u i).M.crest) else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with h
      · have hh:0≤Menu.sumFee (u i) w:=mul_nonneg (Poly.worth B.radii _).le (norm_nonneg _)
        exact (mul_le_mul_of_nonneg_left (bills i hi h) hh).trans_eq (by unfold Menu.fare BudgetPoint.mass; ring)
      · simp
    _ ≤ _ := by rw [←Finset.mul_sum];exact mul_le_mul_of_nonneg_left paid hp

end YM.Integration.WilsonLongContactPriorWeights
