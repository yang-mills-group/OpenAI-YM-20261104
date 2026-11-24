import YM.Integration.WilsonMatrixOriginalDeckPaidPath
import YM.Integration.WilsonGaussianProbeMatrix
import YM.Integration.WilsonMatrixTicketLanesReportedWindow

/-! All-height signed Gram measurements on the physical campaign carrying the nonzero Ward panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckMeasured
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open Trace.Pilot Table Ward PhysMS RG17 RG12 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato
open Pier.Lair SharpGram SharpGram.Lenses WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckPath
open WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckFiledDebit
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {O:Booked B} {S:Table R.family.book} {f:Extraction.Order}
variable (F:Spec.Final R.family f S) (L:Layout F) (J:ℝ→PhysMS.tower S) (h:ℕ)


/-- The same positive localized test and presold boundary fields work for all dates and regulators. -/
def Intake (M : MS_Data G O) : Prop :=
  ∀ {p:E4}, (0:E4)≠p → ∀U:Set (Points 2), U∈𝓝 (Extra.FD.couple 0 p) →
    ∃ (g:Test 2) (A C:ℝ) (e:ℕ),1≤A ∧ 0<C ∧ tsupport g⊆U ∧ (∀x,(g x).im=0 ∧ 0≤(g x).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫x,g x)=1 ∧ (∀μ,IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) ∧
      ∃Z:Set ℝ,Z∈trail ∧ ∃w:(r:Z)→Glyph B h→R.family.label h,
        (∀r:Z,0<r.val ∧ R.family.ref h≤L.level r.val ∧ ∀a,mass R.family h (L.shift h r.val (w r a))≤
          R.family.path.levels.clock.hatBeta (L.level r.val)^e*‖WilsonMatrixOriginalDeckColumns.basis R.family B h a‖ ∧
          master L h r.val (w r a)=J r.val h (WilsonMatrixOriginalDeckColumns.basis R.family B h a)) ∧
        ∀η:ℝ,0<η → ∃W:Set ℝ,W∈trail ∧ ∀ (r:ℕ→Z) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ)
          (n:ℕ) (pos:∀i,0<(r i).val),Monotone (fun i=>(r i).val) → (∀i≤n,(r i).val∈W) →
          ∀(u:Filter (ℕ×ℕ)) [u.NeBot],u≤L.lens → ∀δ:ℝ,0≤δ →
            (∀ᶠz in u,debit R B F L h g (fun i=>(r i).val) pos (fun i=>w (r i)) V n z≤δ) →
            amount (steps V n-change B J h (r n).val (r 0).val) ≤ A^2*((r n).val/(r 0).val)^η*(C*δ)*Real.exp (A*(C*δ))

open Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open Source FVA2 FVA2.Register WilsonPositionHomogeneousFrame RGComparison.Core16 OPE.Therm
open Trace.Sundial Spin WilsonLimitConstruction Precision MS.Land
open WilsonMatrixOriginalFundedPanel
universe u

/-- Both measurements use exactly the same strongly selected cutoff order, hierarchy and layout. -/
def Measured {G : Gauge} (R : Run G) (D : Deck G) {O : Booked D} (M : MS_Data G O) (simple : G.Simple) (N : WilsonPrescription G) (Q : MS.Land.Prescription (Press.portDeck G)) : Prop :=
  ∀ (B : ℕ), 17≤B → ∀ v : Extraction.Order,
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (H:(Bel R.family.book).Hierarchy)(J:ℝ→tower S)(A:ℝ→Spin.change S 4)(δ:ℝ→ℝ)(L:Layout F),
      Leading F J ∧ (∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) ∧
      (∀ᶠr in trail,J r 4=A r) ∧ TendC F A δ ∧ Coupling G (glo A) ∧
      L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens≤(v.refine w).fuse ∧
      WilsonGaussianProbeMatrix.Filed F J L Q ∧ WilsonGaussianRecoveredPanel.Observed (H:=H) (U:=L.lens) F J N L B δ (glo A) ∧
      ∀ h : ℕ, Intake R D F L J h M

theorem on_run {G : Gauge} {R : Run G} {T : Campaign R} (W : Campaign.Pillars R T)
    (simple : G.Simple) {ρ : ℝ} (funded : WilsonLimitConstruction.FundedOriginalProperties.{u} simple ρ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    (D : Deck G) {O : Booked D} (M : MS_Data G O) (N : WilsonPrescription G) (Q : MS.Land.Prescription (Press.portDeck G)) : Measured R D M simple N Q := by
  intro B large v
  have record := funded
  obtain ⟨_,_,_,_,_,_,_,_,_,selected,_⟩:=record
  obtain ⟨w,S,F,_,_,_,_,_,fac,_,H,arch,l,bliss,_,A,J,_,_,δ,_,same,_,comp,lead,obey⟩:=selected v
  obtain ⟨u₀,bank,L,pegs,level,lens,_⟩:=WilsonMatrixOriginalFundedPanel.measured_layout simple W funded pace (B:=B) (by omega) F fac
  letI : L.lens.NeBot := L.notbot
  have prior := WilsonMatrixOriginalEarlierPanel.original (F:=F) (J:=J) (Z:=N) (L:=L) (lead:=lead)
    (paid:=obey) (simple:=simple) (funded:=funded) (subsidy:=subsidy) (pace:=pace) (hB:=show 0 < B by omega) (level:=level)
    (U:=L.lens) (chosen:=le_rfl) (bank:=bank) (E:=fac.toServices) (pegs:=pegs)
    same comp.alignment.spun comp.leading comp.coupling
  have date := WilsonMatrixOriginalReportingMargin.captured F J N L lead obey simple W funded subsidy
    pace large level le_rfl comp.coupling prior
  have near := WilsonMatrixTicketLanesReportedWindow.original R L simple pace (show 0 < B by omega) level
  refine ⟨w,S,F,H,J,A,δ,L,lead,obey,same,comp.leading,comp.coupling,level,lens,
    WilsonGaussianProbeMatrix.filed simple W funded F J lead fac.toServices L Q,
    WilsonGaussianRecoveredPanel.receive F J N L comp.coupling date,?_⟩
  intro h p hp U atPair
  exact WilsonMatrixOriginalDeckPaidPath.purchased R D F L J h lead obey bank fac.toServices pegs near M hp U atPair


end YM.Integration.WilsonMatrixOriginalDeckMeasured
