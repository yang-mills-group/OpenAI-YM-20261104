import YM.Integration.WilsonPhysicalHistoryAxialRoom
import YM.Integration.FVA1Physical.Wilson.SignedPacket

/-! Genuine signed physical wallet replacement in the manuscript's axial
conditional at an actual coarse postcard of the original run. The previous
input debit is an explicitly determined regular-chart supremum. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletAxialPacket
open Function Filter Finset Set MeasureTheory Lattice RG RG.Supply Wilson Source Labels Next.Foundations
open Tree Precision Exterior RGComparison.Core16 FVA2.CityHistory
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao
open MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Mosaic
open Push Push.Uniform PhysicalNext.Repeat.Legato FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open WilsonConditionalTaylorLabels WilsonPhysicalHistoryWalletExperiment WilsonPhysicalHistoryWalletDeposit
open WilsonPhysicalHistoryWalletUniformBound
open scoped Classical Topology
variable {G : Gauge}

def cutoff (V : Voice G) (cle : Clear G V) (simple : G.Simple) (H H' : Stage)
    (P : Patch) (K : KernelChoices) (br : P.Branches K G) (p m s : ℕ)
    {D : ℝ} (D0 : 0≤D) (q e : ℝ) : ℝ :=
  (eventually_atTop.mp (signed_packet_transfer V cle simple H H' P K br p m s D0 q e).choose_spec).choose

def aperture (V : Voice G) (cle : Clear G V) (simple : G.Simple) (H H' : Stage)
    (P : Patch) (K : KernelChoices) (br : P.Branches K G) (p m s : ℕ)
    {D : ℝ} (D0 : 0≤D) (q e : ℝ) : ℝ :=
  fluctuationFee (signed_packet_transfer V cle simple H H' P K br p m s D0 q e).choose V D

/-- The measured old source is the very same full signed wallet at date j+1
of this R; the fitted axial input gets only its independently defined chart
subtotal on the previously admitted fields plus the purchased complement. -/
theorem measured (R : Run G) (simple : G.Simple) (V : Voice G) (cle : Clear G V)
    {N per j u cap : ℕ} (ju : j<u) (cut : u<N) (S : Scene R.family.path.levels per cap)
    (F : Forest (R.family.path.levels.clock.op j per).ratio) (tag : (R.family.path.levels.clock.op j per).Choices)
    (a : Roster G) (mask : Finset (Fin a.length)) (o : Fin a.length→Site (R.family.side (u+1) per))
    (i : Fin a.length) (y b : Site (R.family.side (u+1) per)) (part : Bool)
    (late : opens R a ≤ j+1) (p m s : ℕ) {D : ℝ} (D0 : 0≤D) (q e : ℝ) :
    let H:=R.family.path.levels
    let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F tag
    let br: A.S.patch.Branches A.S.kernel G := (H.blocks j per).branches
    let x:=H.clock.hatBeta j
    let hot:=tip G A.S.patch.L x
    let g:=A.fClock
    let width:=aperture V cle simple (H.params j) (H.params (j+1)) A.S.patch A.S.kernel br p m s D0 q e
    let φ:=reading R (N:=N) ju a mask o i y part
    cutoff V cle simple (H.params j) (H.params (j+1)) A.S.patch A.S.kernel br p m s D0 q e ≤ x →
    Season V (H.params j) (H.params (j+1)) x A.pre A.post A.S (courage G A.S.patch.L x) →
    stencilBound (packet ⟨a,mask⟩) ≤ hot^e →
    fiberRate R (j+1) u*birth R (N:=N) a mask o i y b part ≤ hot^e →
    ∀ (Z : Positions (Primary A.c G)) (T : Nesting G A.f),
      ‖g • Z‖ ≤ D*room hot → BankPaid (anchor R ju b) hot s p m 1 T →
      |reading R (N:=N) ju.le a mask o i y part (postcard G A.c g Z) -
        MSbar.Bulk.expect A.S A.pre (postcard G A.c g Z)
          (fun U=>clockReading p g T (chartLog g (canoe (S:=A.S) A.F U)))| ≤
        WilsonPhysicalHistoryAxialRoom.price g (width*room hot) g p T φ + 5*hot^q := by
  intro H A br x hot g width φ gate season Bcap Mcap Z T observed bank
  obtain ⟨Q,registered,meas,bounded,full⟩ :=
    WilsonPhysicalHistoryWalletUniformBound.stored R simple cut ju a mask o i y b part late
  have paid := WilsonPhysicalHistoryAxialRoom.purchased g (width*room hot) g p T φ bounded
  have truePacket:= (eventually_atTop.mp (signed_packet_transfer V cle simple (H.params j)
    (H.params (j+1)) A.S.patch A.S.kernel br p m s D0 q e).choose_spec).choose_spec x gate
  have result := truePacket A rfl rfl season Z (anchor R ju b) observed Q φ T
    (stencilBound (packet ⟨a,mask⟩)) (fiberRate R (j+1) u*birth R (N:=N) a mask o i y b part)
    (Push.Local.kappa R.family.path (j+1)) (WilsonPhysicalHistoryAxialRoom.price g (width*room hot) g p T φ)
    registered.1 registered.2.1 full meas bounded Bcap Mcap (WilsonPhysicalHistoryWalletHardRate.kappa_cap R (j+1))
    paid.1 bank paid.2
  rw [WilsonPhysicalHistoryAxialRoom.next R ju a mask o i y part]
  exact result

end YM.Integration.WilsonPhysicalHistoryWalletAxialPacket

