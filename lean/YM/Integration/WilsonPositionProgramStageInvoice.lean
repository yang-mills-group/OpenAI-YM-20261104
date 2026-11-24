import YM.Integration.WilsonWindowReportingPace
import YM.Integration.WilsonWindowJointPurchase
import YM.FVAAlt2.Rocket.Licenses

/-! The position kernel's finite stage prices on the original pre-period block election. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramStageInvoice
open RG RG.Supply Precision Push.PriceCompiler PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Input Org Progress
open WilsonLimitConstruction.FundedCompanySelection RegulatorIR RegulatorIR.Atlas RegulatorIR.FVAAlt2
open scoped Topology Classical BigOperators ENNReal
variable {G : Gauge}

/-- The stage is the one actually read by the kernel at this step. -/
def Requested : Prediction G := fun {M} {D} {A} _ => ∀ m : ℕ,
  (Lodge.pad (Oracle.books M.p.kernel) M.p.has (A.B.a.clock.J (m+1)) (D.L (A.B.a.clock.J (m+1))) : ℝ) ≤
    Real.log (RG16.Lambda A.B.a m)

theorem prepaid (simple : G.Simple) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Requested G) s price := by
  intro C E flags programs wages baton
  refine ⟨0,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  obtain ⟨W,hVW,grant⟩ := RG16.later D simple V (fun j => (Lodge.pad (Oracle.books s.kernel) s.has j (D.L j) : ℝ))
  refine ⟨W,hVW,?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides m
  exact (le_max_right _ _).trans ((grant Y hY wait B.a B.valid).2 m)

theorem joint (simple : G.Simple) {s : Sheet G} {price : MapPrices} {goal : Prediction G}
    (paid : WilsonFundedWindowMenu.Prepared (@goal) s price) :
    WilsonFundedWindowMenu.Prepared (WilsonWindowJointPurchase.Together (@goal) (@Requested G)) s price :=
  WilsonWindowJointPurchase.joint paid (prepaid simple s price)

theorem bill {K : KernelChoices} (Z : ∀ P : RG.Patch, P.Branches K G) (P : RG.Patch) (p : ℕ) (hp : p ≤ P.J) :
    (glowF G (Oracle.books K) Z p (Lodge.through p) P + glowPage G (Oracle.books K) (Lodge.through p) P.J).toReal ≤
      (Lodge.pad (Oracle.books K) Z P.J P.L : ℝ) := by
  let Y := Oracle.books K
  let f := fun q => Lodge.Track.bills G Y P.J P.L.val Z q (Lodge.through q)
  have one : f p=glowF G Y Z p (Lodge.through p) P + glowPage G Y (Lodge.through p) P.J := by
    change (if h:4 ≤ P.J ∧ 3 ≤ P.L.val ∧ Odd P.L.val then _ else _) = _
    rw [dif_pos ⟨P.order_cut,P.coarse,P.odd_side⟩]
    rfl
  have finite : (Finset.range (P.J+1)).sup f ≠ ⊤ := by
    exact (Lodge.afford Y Z P.J P.L).ne
  rw [←one]
  exact (ENNReal.toReal_mono finite (Finset.le_sup (Finset.mem_range_succ_iff.mpr hp))).trans (Nat.le_ceil _)

end YM.Integration.WilsonPositionProgramStageInvoice
end
