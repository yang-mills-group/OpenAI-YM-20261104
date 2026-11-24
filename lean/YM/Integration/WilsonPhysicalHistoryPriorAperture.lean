import YM.Integration.WilsonPhysicalMarkedDefectSingletonRent

/-! The whole true spatial strip of a previously issued graduate can be priced before all cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryPriorAperture
open Function Filter Set Finset Lattice Wilson RG RG.Supply Source Pressure Input Org Precision
open Progress.DirectedRecipe Payments Push.AbsoluteSums Push.PriceCompiler
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore QuadraticLocal.Syl
open Marker RG3.Annuncia MergeProof.Accent FVA1Physical.Round2.Curvature FVA1Physical.Round2.CP5
open scoped Topology BigOperators Classical

variable {G:Gauge} {M:Metals G} (D:Rolls M.p)
    (S:Roots (G:=G) M.p.profile M.K M.p.kernel) (φ:ℕ→ℕ)

def Paid {P:Protection D} (W:Delays P) : Prop:=
  ∀(x k:ℕ),k ≤ x → ∀t:ℝ,W.betaEntry x ≤ t → Real.exp ((Poetry.Agenda.seed S φ (Burn.horizon k) x)⁻¹^2) ≤ t

theorem priced {P:Protection D} (W:Delays P) :
    ∃ V : Delays P, DelayLe W V ∧ ∀ Z : Delays P, DelayLe V Z → Paid D S φ Z := by
  let F(x:ℕ)(t:ℝ):=∀k∈Finset.Iic x,Real.exp ((Poetry.Agenda.seed S φ (Burn.horizon k) x)⁻¹^2) ≤ t
  have occur(x:ℕ):∀ᶠ t:ℝ in atTop,F x t:=
    (eventually_all_finset (Finset.Iic x)).2 (fun k _=>eventually_ge_atTop _)
  obtain ⟨A,_,lower,agenda⟩:=collect_upper W.betaEntry F occur
  refine ⟨{W with betaEntry:=A},⟨lower,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro Z growth x k hk t ht
  exact agenda x t ((growth.1 x).trans ht) k (Finset.mem_Iic.mpr hk)

def law (G:Gauge) (φ:ℕ→ℕ) : VowsR.LawScroll G φ where
  clause M D _ _ _ _ _ _ _ _ S _ _ _ W := Paid (M:=M) D S φ W
  permits := by
    intro s T Q C E he
    refine ⟨fun _=>0,?_⟩
    intro ℓ _ D q Wp Z Q' S' h Pw T₀ Y B hP W
    exact priced (M:=ThroughLaunch.currency s T ℓ) D Q φ W

theorem on_run (simple:G.Simple) (R:Run G)
    (F:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ:ℕ→ℕ) (paid:Paid R.rolls F φ R.alloy.delay)
    (b k:ℕ) (fit:k ≤ R.alloy.B.a.clock.J (b+1)) :
    (Poetry.Agenda.seed F φ (Burn.horizon k) (R.alloy.B.a.clock.J (b+1)))⁻¹^2 ≤ Real.log (R.alloy.B.a.clock.hatBeta (b+1)):=by
  have price:=paid _ k fit _ ((R.alloy.B.valid.pays b).trans (Push.Corrected.Last.band_le R.alloy.B.a simple (Nat.le_succ b)))
  exact (Real.log_exp _).symm.le.trans (Real.log_le_log (Real.exp_pos _) price)

end YM.Integration.WilsonPhysicalHistoryPriorAperture
