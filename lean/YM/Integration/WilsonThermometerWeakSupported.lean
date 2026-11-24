import YM.Integration.WilsonThermometerWeakPublication
import YM.Integration.WilsonThermometerOriginalMeans
import YM.Integration.WilsonThermometerMarchSupported

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSupported
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonPositionCorrectedCap WilsonSeparatedOriginalThermometerCells
open RG12 RG05Readout.Address WilsonThermometerOffsetTrajectory RG05Readout
open MergeProof Cells Labels Bid Push Extra.Histories Next.Extract PhysicalNext.Repeat Legato Bandage
open WilsonThermometerMarchProduct (field)
open WilsonThermometerFundedWeakCells (candidate extra)
open WilsonThermometerMarchSupported (period)
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable {H : (Bel R.family.book).Hierarchy} {Y:Ultrafilter (ℕ×ℕ)}
local notation "d" => WilsonThermometerFundedWeakCells.degree

theorem unmask (Z:Group R.family 6) (checked:Z.station.checked f H Z.horizon)
    (fixes:∀j : Fin 7,Z.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j) :
    ∀ᶠ z:ℕ×ℕ in f.fuse, ∀ k (h:k≤z.1) (s:Badge) (Q:(i:Fin 3)→Emblems R.family (d i))
      (y:(i:Fin 3)→Palette R.family (d i)) (o:Fin 3→Site (R.family.side z.1 z.2))
      (U:Config G (R.family.side z.1 z.2)),
      (∏ i,R.family.O z.1 z.2 (candidate (p:=z.2) Z h s Q y i) (o i) U) =
        ∏ i∈s,R.family.O z.1 z.2 (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h (y i)) (o i) U := by
  filter_upwards [eventually_all.mpr (fun i:Fin 3=>
    WilsonPositionThermometerStationUnit.original Z.station (index Z (grade i)) R.makes checked)] with z bank k h s Q y o U
  have per (i:Fin 3) : R.family.O z.1 z.2 (candidate (p:=z.2) Z h s Q y i) (o i) U =
      if i∈s then R.family.O z.1 z.2 (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h (y i)) (o i) U else 1 := by
    by_cases hi:i∈s
    · simp [candidate,hi]
    · simp only [candidate,if_neg hi]
      change R.family.O z.1 z.2 (Z.station.wheel.atCut z (index Z (grade i)) (Z.change (grade i) (source R.family s i))) (o i) U = 1
      rw [WilsonPositionThermometerGradedSource.unit R.family s i hi,fixes]
      exact congrFun ((bank i).2 (o i)) U
  simp_rw [per]
  simp

variable (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (V : Store G) (A : ℝ→Group R.family 6)

theorem original (simple : G.Simple) (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J)
    (E : ∀ n, SectionData (R.family.labels.level n)) (W : Mark.Weave G)
    (P : ∀ n, (ℕ×ℕ)→R.family.label n ≃ₗ[ℂ] R.family.label n) (b : Presentation R.family)
    (portfolio : ∀ n,Mark.Portfolio R.family.params (E n) (W n))
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a))
    (φ : Test 3) (legal : tsupport φ⊆conf 3) :
    ∃ start : ℕ, ∀ᶠ r in trail, let Z:=adjusted F J V A r
      ∀ w≥start, ∃ M:Badge→ℝ, (∀s,0≤M s) ∧ ∀ᶠ z:ℕ×ℕ in f.fuse, ∃ h₀:w≤z.1,
      ∀ (s:Badge) (o:Fin 3→Site (R.family.side z.1 z.2)), (∃ x∈tsupport φ,positions (R:=R) r z x=o) →
      ∀ (B : ℕ→ℕ→ℝ) (X₀ : (i:Fin 3)→Sight R.family (d i) z.2) (Q : (i:Fin 3)→Emblems R.family (d i)),
      (∀ i,Enrolled R.makes R.doors B w z.1 z.2 (d i) (WilsonThermometerOffsetResidue.digits R z.1 z.2 (o i)) (X₀ i) (Q i)) →
      ∀ y : (i:Fin 3)→Palette R.family (d i),
      (∀i∈s,b.step (d i) z (field Z z.1 z.2 Finset.univ i) =
        b.step (d i) z (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h₀ (y i))) →
      ‖Wilson.moment (R.family.beta z.1 z.2) (fun U=>∏i∈s,R.family.O z.1 z.2
          (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h₀ (y i)) (o i) U) - row Z z o s‖ ≤
        7*(Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*(M s+extra y)^3) := by
  obtain ⟨radius,start,ready⟩:= WilsonThermometerFundedWeakCells.original F J V A simple book lead E W P b portfolio house
  obtain ⟨p₀,scope⟩:=WilsonThermometerCompactChambers.intersects R φ legal E radius d
  refine ⟨start,?_⟩
  filter_upwards [ready,WilsonPositionCorrectedCap.original F J V A book lead 0,
    show ∀ᶠ r:ℝ in trail,0<r from self_mem_nhdsWithin,
    show ∀ᶠ r:ℝ in trail,r<1 from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds zero_lt_one)] with r programs filed rp limit
  dsimp only
  intro w hw
  let Z:=adjusted F J V A r
  obtain ⟨m,fr⟩:=(scope r rp limit.le).exists
  obtain ⟨k,geom,registered⟩:=(fr.and (programs w hw)).exists
  obtain ⟨early,fit⟩:=geom
  obtain ⟨M,positive,works⟩:=registered
  refine ⟨M,positive,?_⟩
  filter_upwards [works,(WilsonThermometerMarchTerminalWatch.upper f).eventually fit,
    (period f).eventually_ge_atTop p₀,unmask Z filed.2.1 (fun j=>(filed.2.2.2.2.1 j).2.1)] with z authentic valid hp restore
  obtain ⟨h,h₀,offer⟩:=authentic
  refine ⟨h₀,?_⟩
  intro s o live B X₀ Q record y eq
  obtain ⟨u,v,hv,avoid,inside⟩:=valid.choose_spec z.2 hp o live
  let T:=center R.family.S z.2 (early.trans h) 0
  let w₀:Empty→T.Cell:=Empty.elim
  let exterior:Empty → Config G (R.family.side z.1 z.2)→ℂ:=Empty.elim
  have one : WilsonThermometerReflectedWatch.exterior T w₀ exterior = (fun _=>1) := by
    funext; simp [WilsonThermometerReflectedWatch.exterior]
  have different : Function.Injective (Sum.elim v w₀) := by
    rintro (a|a) (c|c) rel
    · exact congrArg Sum.inl (hv rel)
    all_goals first | exact Empty.elim a | exact Empty.elim c
  have hearing:=offer s m early v _ avoid inside o B X₀ Q record y eq Empty w₀ exterior different (fun i=>Empty.elim i)
  rw [one] at hearing
  have got:=hearing (fun _ _ _ _=>rfl) (Mark.cont_envelope continuous_const)
  let c := candidate (p:=z.2) Z h₀ s Q y
  have amount : WilsonThermometerMarchSupported.read R.family z c o =
      Wilson.moment (R.family.beta z.1 z.2) (fun U=>∏i∈s,R.family.O z.1 z.2
        (WilsonThermometerWeakEquationCost.column R (p:=z.2) (Q i) h₀ (y i)) (o i) U) := by
    unfold WilsonThermometerMarchSupported.read
    congr 1
    funext U
    exact restore w h₀ s Q y o U
  rw [←amount]
  change ‖WilsonThermometerMarchSupported.read R.family z c o - WilsonThermometerMarchSupported.read R.family z (field Z z.1 z.2 s) o‖ ≤ _
  rw [←WilsonThermometerMarchSupported.translate R.family z c o u,←WilsonThermometerMarchSupported.translate R.family z (field Z z.1 z.2 s) o u]
  simpa [WilsonThermometerMarchSupported.read,c] using! got

end YM.Integration.WilsonThermometerWeakSupported
end

