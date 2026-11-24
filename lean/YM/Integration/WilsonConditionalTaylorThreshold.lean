import YM.Integration.WilsonWindowReportingPace
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! Prepay the moving Wilson comparison on the original selected rolls. The threshold
depends on both actual stages and the chosen block, and is paid before the period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThreshold

open Function Filter Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch Push.PriceCompiler Progress.DirectedRecipe Next.Foundations
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology

variable {G : Gauge}

abbrev Fare := Stage → Stage → Patch → KernelChoices → ℝ

def Paid (fare : MapPrices → Fare) : Prediction G := fun {M} {_} {A} _ =>
  ∀ j n, fare M.K (A.B.a.params j) (A.B.a.params (j+1)) (A.B.a.clock.op j n).patch
    (A.B.a.clock.op j n).kernel ≤ A.B.a.clock.hatBeta j

/-- Raise only the existing beta entry after the physical rolls have fixed their
block lengths. This single invoice covers every regulator cutoff and period. -/
theorem prepaid (fare : MapPrices → Fare) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Paid G fare) s price := by
  intro costs expenses flags programs wages baton
  refine ⟨0,?_⟩
  intro l hl D w v Z post scouts pocket θ records P menu V quarter
  let Y := ThroughLaunch.raise s l
  let request (a : ℕ) (x : ℝ) := ∀ i ≤ a, ∀ patch : Patch, patch.J=a → patch.L=D.L a →
    fare price (Y.profile i) (Y.profile a) patch Y.kernel ≤ x
  have buy (a : ℕ) : ∀ᶠ x : ℝ in atTop, request a x := by
    by_cases ha : 4 ≤ a
    · let patch : Patch := ⟨D.L a,a,ha,(D.large a).size,(D.large a).odd⟩
      have h := (Finset.range (a+1)).eventually_all.mpr (fun i _ =>
        eventually_ge_atTop (fare price (Y.profile i) (Y.profile a) patch Y.kernel))
      filter_upwards [h] with x prices
      intro i hi q hJ hL
      have eq : q=patch := by cases q; unfold patch; congr
      exact eq ▸ prices i (Finset.mem_range.mpr (by omega))
    · exact .of_forall fun _ _ _ p hp _ => (ha (hp ▸ p.order_cut)).elim
  choose u grant using fun a => eventually_atTop.mp (buy a)
  let W : Delays θ := {V with betaEntry:=fun a => max (V.betaEntry a) (u a)}
  refine ⟨W,⟨fun _ => le_max_left _ _,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' later bar wait priced B archive shape rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides j n
  let a := B.a.clock.J (j+1)
  have profile (i : ℕ) : B.a.params i=Y.profile (B.a.clock.J i) := by
    unfold Levels.params Calendar.params
    rw [B.valid.stage]
  change fare price (B.a.params j) (B.a.params (j+1)) (B.a.clock.op j n).patch B.a.clock.kernel ≤ _
  rw [profile j,profile (j+1),B.valid.kernel]
  refine grant a _ ((le_max_right _ _).trans ((later.beta a).trans (B.valid.pays j)))
    _ (B.a.fits.mono (Nat.le_succ j))
    (B.a.clock.op j n).patch rfl ?_
  change B.a.S.block j=D.L a
  rw [←B.a.fits.sameFactor,B.valid.lengths]

def cap (i : ℕ) : ℕ := i-1

theorem cap_mono : Monotone cap := fun _ _ h => Nat.sub_le_sub_right h 1

/-- One growing reserve meets all four finite calls (coupling, field, geometry and
external displacement); the height is chosen before the cutoff, torus, or background. -/
theorem eventually_admitted (R : Run G) (p m D : ℕ) : ∀ᶠ k : ℕ in atTop,
    5 ≤ R.alloy.B.a.clock.J k ∧ p+4 ≤ cap (R.alloy.B.a.clock.J k) ∧
    6 ≤ cap (R.alloy.B.a.clock.J k) ∧ m+1 ≤ cap (R.alloy.B.a.clock.J k) ∧
    D ≤ cap (R.alloy.B.a.clock.J k) := by
  filter_upwards [R.alloy.B.a.fits.deep.eventually_ge_atTop (p+m+D+8)] with k h
  unfold cap
  omega

/-- The needed increasing jet reserve follows from the original stage profile;
there is no second choice of cutoff, sheet, or run. -/
theorem jets (R : Run G) (orders : ∀ a, a ≤ (R.metals.p.profile a).order) (j : ℕ) :
    cap (R.alloy.B.a.clock.J j)+1 ≤ (R.alloy.B.a.params j).order := by
  have profile : R.alloy.B.a.params j = R.metals.p.profile (R.alloy.B.a.clock.J j) := by
    unfold Levels.params Calendar.params
    rw [R.alloy.B.valid.stage]
  rw [profile]
  have h := orders (R.alloy.B.a.clock.J j)
  have six := (R.metals.p.profile (R.alloy.B.a.clock.J j)).order_ge
  unfold cap
  omega

end YM.Integration.WilsonConditionalTaylorThreshold
end

