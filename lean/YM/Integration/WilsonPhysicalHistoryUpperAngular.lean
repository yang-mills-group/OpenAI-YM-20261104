import YM.Integration.WilsonPhysicalMarkedDefectSelectedHistory
import YM.Integration.FVA1Physical.Wilson.SparsePhysical

/-! Buy the actual sparse gauge chart on the very same physical company
and time schedule, before any cutoff, period, target links, or threshold
exponent are specified. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryUpperAngular
open Function Filter Set Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Qlocal.Schedule
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature PhysicalNext.Repeat.Legato
open WilsonLimitConstruction.FundedCompanySelection WilsonWindowJointPurchase
open scoped Classical Topology BigOperators
variable {G : Gauge}

def angular (G : Gauge) : Prediction G := fun {M D A} K => selectedThreshold (angularThreshold G) M D A K

theorem prepaid (G : Gauge) : WilsonFundedWindowMenu.AllPrices (@angular G) := by
  intro s T R E flags C z bt
  let f := angularThreshold G
  refine ⟨fun _ => 0,?_⟩
  intro l hl D w v Z F S pocket P records cost menus V quarter
  let Y := ThroughLaunch.raise s l
  let test (a : ℕ) (x : ℝ) := ∀ i ≤ a, ∀ patch : Patch, patch.J=a → patch.L=D.L a →
    f (Y.profile i) (Y.profile a) patch Y.kernel ≤ x
  have buy (a : ℕ) : ∀ᶠ x : ℝ in atTop, test a x := by
    by_cases ha : 4 ≤ a
    · let patch : Patch := ⟨D.L a,a,ha,(D.large a).size,(D.large a).odd⟩
      have h := (Finset.range (a+1)).eventually_all.mpr (fun i _=>
        eventually_ge_atTop (f (Y.profile i) (Y.profile a) patch Y.kernel))
      filter_upwards [h] with x prices
      intro i hi P hP hL
      have eq : P=patch := by cases P; unfold patch; congr
      exact eq ▸ prices i (Finset.mem_range.mpr (by omega))
    · exact .of_forall fun x i hi p hp _=>(ha (hp ▸ p.order_cut)).elim
  obtain ⟨u,_,hu,paid⟩ := collect_upper V.betaEntry test buy
  let W : Delays P := {V with betaEntry:=u}
  refine ⟨W,⟨hu,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' later bar wait priced B archive origins shape
  dsimp only
  intro η q exchange aux rider booth sheltered works hand j n
  let a := B.a.clock.J (j+1)
  have profile (i : ℕ) : B.a.params i=Y.profile (B.a.clock.J i) := by
    unfold Levels.params Calendar.params
    rw [B.valid.stage]
  change f (B.a.params j) (B.a.params (j+1)) (B.a.clock.op j n).patch B.a.clock.kernel ≤ _
  rw [profile j,profile (j+1),B.valid.kernel]
  refine paid a _ ((later.beta a).trans (B.valid.pays j)) _ (B.a.fits.mono (Nat.le_succ j))
    (B.a.clock.op j n).patch rfl ?_
  change B.a.S.block j=D.L a
  rw [←B.a.fits.sameFactor,B.valid.lengths]


theorem jointPrice (more : Prediction G) (bought : WilsonFundedWindowMenu.AllPrices (@more)) :
    WilsonFundedWindowMenu.AllPrices (fun K => more K ∧ angular G K) :=
  fun s T => joint (bought s T) (prepaid G s T)

end YM.Integration.WilsonPhysicalHistoryUpperAngular
end
