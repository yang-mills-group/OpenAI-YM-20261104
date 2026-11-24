import YM.Integration.WilsonConditionalTaylorPurchase
import YM.Integration.WilsonReportCitizenRun
import YM.Integration.FVA1Physical.Wilson.PacketPosteriorRun

/-! All finite conditional Wilson expansions on one funded physical trajectory.
Each precision is paid before choosing the period, cutoff, field, or polynomial bank. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorPosterior

open Function Filter Set Finset Lattice RG RG.Shoot YM.Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection Next.Foundations
open MSbar MSbar.Heath MSbar.Ballet MSbar.Mosaic MSbar.Bulk MSbar.Rolling MSbar.Lis
open MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Bakery.Film MSbar.Midpoint
open Exterior Tree Push.Uniform FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open Qlocal.Schedule WilsonConditionalTaylorThreshold WilsonConditionalTaylorCalendar
open WilsonWindowJointPurchase
open scoped Classical Topology BigOperators

universe u
variable {G : Gauge}

abbrev Ticket := ℕ × ℕ × ℕ × ℕ × ℕ

def fare (V : Voice G) (cle : Clear G V) (simple : G.Simple) (r : Ticket) : MapPrices → Fare :=
  fun _ => fullPacketGate V cle simple r.1 (6+r.2.1) (r.2.2.1+1) (by omega)
    (Nat.cast_nonneg (α:=ℝ) r.2.2.2.1) (loss_pos r.2.2.2.2) (loss_small r.2.2.2.2 r.1)

def tariff (V : Voice G) (cle : Clear G V) (simple : G.Simple) : MapPrices → Fare :=
  fun M H H' P K => max 4 (atlas (fare V cle simple) M H H' P K)

/-- The original RG conditional against the polynomial obtained by the
independent joint Gaussian, with input chart on the actual uncut fine links.
The degree-zero gate is removed for nonconstant external sources by suspending
both their input and output one coupling order. -/
def Posterior (R : Run G) (u : G.ColorIndex) : Prop :=
  ∀ p s m D : ℕ, ∀ {η : ℝ}, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k : ℕ in atTop,
    ∀ N n, k ≤ N →
      (∃ S : Scene R.family.path.levels n (p+2), Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S) ∧
      ∀ (S : Scene R.family.path.levels n (p+2)) (scene : Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S)
        (j : ℕ) (kj : k ≤ j) (jN : j < N),
        let F := (scene.step j jN kj).choose
        let v := (scene.step j jN kj).choose_spec.choose
        let A := sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
        let y := R.family.path.levels.clock.hatBeta (j+1)
        let g := A.fClock
        S.Poly j=A.Zpost R.metals.O ∧ ∀ (b : Site A.f) (Z : Positions (Primary A.c G)) (T : Nesting G A.f),
          ‖g • Z‖ ≤ D*room y → BankPaid b y (6+s) p (m+1) δ T → (PowerSeries.coeff 0 T).totalDegree=0 →
          |expect A.S A.pre (postcard G A.c g Z) (fun w => clockReading p g T (chartLog g (canoe (S:=A.S) A.F w))) -
            clockReading p g (emittedRows A R.metals.O (enterRows A T) p) Z| ≤ g^((p:ℝ)+1-η)

theorem read (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G) (cle : Clear G V)
    (inventory : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
    (catalogue : Paid (tariff V cle simple) R.kit) : Posterior R u := by
  obtain ⟨frame,fields,vac⟩ := inventory
  have allFees : Paid (atlas (fare V cle simple)) R.kit := fun j n => (le_max_right ..).trans (catalogue j n)
  have large (j : ℕ) : 4 ≤ R.family.path.levels.clock.hatBeta j := (le_max_left ..).trans (catalogue j 0)
  intro p s m D η positive
  obtain ⟨t,loss_le⟩ := cofinal positive
  let q := loss t
  have pos : 0 < q := loss_pos t
  have below : q < (p:ℝ)+1 := loss_small t p
  let δ := packetReserve (p+2) (m+1) (div_pos (half_pos (half_pos pos)) (by norm_num : 0 < (8:ℝ)))
  have threshold := WilsonConditionalTaylorCalendar.read R (fare V cle simple) allFees (p,s,m,D,t)
  have all := packet_posterior_on simple R u V cle frame p (6+s) (m+1) (by omega) (by omega)
    (Nat.cast_nonneg (α:=ℝ) D) pos below threshold fields vac
  refine ⟨δ,packetReserve_pos ..,?_⟩
  filter_upwards [all] with k fund N n includeHeight
  obtain ⟨has,quote⟩ := fund N n includeHeight
  refine ⟨has,?_⟩
  intro S scene j kj jN F v A y g
  obtain ⟨same,bound⟩ := quote S scene j kj jN
  refine ⟨same,?_⟩
  intro b Z T small bank flat
  have beta : 1 ≤ (R.family.path.rep N n (j+1)).beta := by
    have edge := (R.T.choice.represents N n (j+1) jN).band.1
    change R.family.path.levels.clock.hatBeta (j+1)/2 ≤ (R.family.path.rep N n (j+1)).beta at edge
    linarith [large (j+1)]
  have unit : g ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr beta)
  have posg : 0 < g := inv_pos.mpr (Real.sqrt_pos.2 (zero_lt_one.trans_le beta))
  exact (bound b Z T small bank flat).trans
    (Real.rpow_le_rpow_of_exponent_ge posg unit (sub_le_sub_left loss_le _))

/-- Select alongside any other prepaid physical data. The posterior uses the
same run whose marked correlations, continuum existence and charged log are emitted. -/
theorem select (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (u : G.ColorIndex) (V : Voice G) (cle : Clear G V)
    (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      more R.kit ∧ WilsonConditionalTaylorPurchase.Inventory u V R.kit ∧ Posterior R u ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧
      PhysicalNext.Repeat.Legato.Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨R,T,W,⟨extra,inventory,catalogue⟩,_,_,_,corr,original,citizen,logBook⟩ :=
    WilsonReportCitizenRun.select.{u} simple hε (Together (@more) (Together
      (@WilsonConditionalTaylorPurchase.Inventory G u V) (@Paid G (tariff V cle simple))))
      (fun s M => joint (credit s M) (joint (WilsonConditionalTaylorPurchase.prepaid simple u V cle s _)
        (WilsonConditionalTaylorThreshold.prepaid (tariff V cle simple) s _)))
  exact ⟨R,T,W,extra,inventory,read R simple u V cle inventory catalogue,corr,original,citizen,logBook⟩

end YM.Integration.WilsonConditionalTaylorPosterior
end

