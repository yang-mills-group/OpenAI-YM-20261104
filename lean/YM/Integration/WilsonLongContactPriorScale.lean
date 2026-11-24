import YM.RemainderComparison.Lyric.Flux
import YM.Integration.WilsonLongContactPriorWeights
noncomputable section
namespace YM.Integration.WilsonLongContactPriorScale
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

open RemainderComparison.Lyric

theorem roster {Z:Type} [Fintype Z] (s:V→Site f) (M:Z→Menu.Hat Γ Y) (w:V→ℝ)
    (positive:∀i,0<w i) (δ:ℝ) (invoice:Menu.Offer s M w Y.p.B Y.p.supportExponent δ):
    Scale s (fun i=>(M i).s.val) (fun i=>(M i).M) (fun i=>Menu.sumFee (M i) w)
      (Fintype.card V) Y.p.supportExponent δ S:=by
  constructor
  · exact fun i=>Menu.timed (M i) positive
  · intro i _
    obtain ⟨v,hv⟩:=(M i).shiny
    exact ⟨v,hv,invoice.sites i (Finset.mem_image_of_mem _ hv)⟩
  · intro v
    apply budget_mono (invoice.budget (s v))
    · intro i
      split_ifs
      · exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Menu.timed _ positive) (M i).M.profit)
      · exact le_rfl
    · intro i
      by_cases hv:v∈(M i).s.val
      · have loc:=invoice.sites i (Finset.mem_image_of_mem s hv)
        simp only [if_pos hv,if_pos loc]
        unfold Palette.wages Menu.fare
        ring_nf
        exact le_rfl
      · simp only [if_neg hv]
        split_ifs
        · exact mul_nonneg (Menu.Crew w positive) (Real.exp_nonneg _)
        · exact le_rfl
  · simpa only [Finset.sum_empty] using budget_sum (invoice.budget (0:Site f)) ∅
  · intro y
    exact (Finset.card_le_univ _)

theorem original (base x:X) (E:Finset ℕ) (K:Finset (ℕ×ℕ)):
    let hats:=(promised B base x E K).terms
    Scale seats (fun i=>(hats i).s.val) (fun i=>(hats i).M) (fun i=>Menu.sumFee (hats i) w)
      (Fintype.card V) Y.p.supportExponent (2*((Fintype.card V:ℝ)*a+(Fintype.card V:ℝ)*(κ*b))) S:=by
  intro hats
  exact roster _ hats w B.radii _ (ManuscriptQLocalMarkedRoster.offer B base x E K)

end YM.Integration.WilsonLongContactPriorScale
