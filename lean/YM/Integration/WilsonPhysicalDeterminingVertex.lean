import YM.Integration.WilsonOrdinaryNestedEnrollment
import YM.Integration.WilsonPublicForkPublicRows

/-! Two prescribed ordinary readings on the same original cutoffs fund a comparable vertex. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalDeterminingVertex
open Function Filter Set MeasureTheory Extraction Table Spec OPE OPE.Orbits OPE.Log RG17
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open Maxwell XSpace XSpace.Normalize FVA2.O FVA2.O.Score MS MS.Land MS.Fleet MS.Theater
open Next.Rank RG12 SharpGram WilsonPositionHomogeneousFrame WilsonMSDictionaryVector
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonPublicOutputSmooth WilsonPublicOutputRegulators
open EveryPhase GapsContact GapsContact.Seams GapsContact.Ascent Trace.Terrace Frontier6 Frontier6.Tale
open YM.Integration.WilsonLimitConstruction
open scoped Classical Topology BigOperators
universe u
variable {G:Gauge} {R:Run G} {T:Campaign R}{W:Campaign.Pillars R T} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
    {simple:G.Simple} {σ:Prescription (Press.portDeck G)} {branch:Bool} (ms:Main.Match Z simple M σ branch)


local notation "θ" => reading F J Z
open WilsonOrdinaryNestedBasis WilsonOrdinaryNestedSmoothTree WilsonViewerElectedHierarchy


variable {n h:ℕ} {d:Fin n→ℕ}
open WilsonOrdinaryNestedEnrollment (Names Panel wage)
open WilsonPublicForkPublicRows (probe)

/-- The full children with one actual exterior, and each output-basis field with that same exterior. -/
def Rows (L : Layout F) (B : Profiles R h) (w : B.probes.index → Atom (R:=R) h)
    (issued : ∀ j, B.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
    (A P q : ℕ) (v : ∀ i, Free R.family (d i)) (r : ℝ) (tp : 0 < r / ((θ r)^A)^2)
    (names : Names R d h) (ψ : Test n) (a b : ℝ) : Prop :=
  let X := WilsonPublicOutputSmooth.exterior F J Z B w issued tp
  let φ := fun j => profile (B.probes.shell j) (w j) (issued j) (test B j)
  let s := WilsonPublicForkIndependentPlacement.age A (θ r)
  let amp := (∏ i, ‖v i‖) * Read.Value ψ
  let toll := (θ r)^(P + A*(2*h+1))
  f.late fun N per =>
    (∀ j, ‖packMark L (X j) d names.1 r ψ (N,per) -
      WilsonPublicForkIndependentFields.full R.family d h Z q (θ r) s v (probe B w j) ψ (φ j)‖ ≤ a*amp*toll) ∧
    (∀ k j, ‖headMark L (X j) h r (N,per) (names.2 k) -
      WilsonPublicForkIndependentFields.gram R.family h Z q (θ r) s (probe B w j) (φ j) k‖ ≤ b*toll)

def Paid (L : Layout F) (K : Set (Points n)) (P q : ℕ) (X : Panel R d h) : Prop :=
  ∀ c, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ᶠ r in trail,
    ∀ tp : 0 < r / ((θ r)^X.rise)^2, ∀ ψ : Test n, tsupport ψ ⊆ K →
      Rows F J Z L X.B X.w X.issued X.rise P q (axes (R:=R) d c) r tp (X.labels c r) ψ a b

private theorem scheduled {T:Type*} [Nonempty T] {D:ℝ→T→Prop} (h:∀ᶠr in trail,∃u,D r u):
    ∃a:ℝ→T,∀ᶠr in trail,D r (a r):=by
  classical
  refine ⟨fun r=>if good:∃u,D r u then good.choose else Classical.choice (inferInstance:Nonempty T),?_⟩
  filter_upwards [h] with r good
  simpa only [dif_pos good] using good.choose_spec

include ms in
theorem original {κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (pace:WilsonWindowReportingPace.Slow R.kit)(V:XSpace.Normalize.Store G)
    {course:Almanac F}{Y:(Bel R.family.book).Hierarchy}{U0:Ultrafilter (ℕ×ℕ)}{arc:Arch R.family}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}(run:Selected.{u} F course Q J Y arc U0 simple cohort)
    (report:ℕ)(positive:0<report)(clock:Coupling G θ)(d:Fin n→ℕ)(h:ℕ)(U η:ℝ)(sep:0<η):
    let level:=WilsonMeasuredWindow.stop R.family.path.levels simple report
    let shift:=fun (d:ℕ) (_:ℝ)=>LinearEquiv.refl ℂ (R.family.label d)
    let L:=WilsonOriginalBlissObserved.layout F run.bliss J level shift
    L.lens=(U0:Filter UVIndex) ∧ ∃E:ℕ,∀P q, P+(P+E+1)*(2*h+1) ≤ q → ∃X:Panel R d h,
      X.rise=P+E+1 ∧
      (∀c,∃a e,∀ᶠr in trail,0<r/((θ r)^X.rise)^2 ∧
        wage F J Z L (axes (R:=R) d c) a e r (X.labels c r)) ∧
      (Paid F J Z L (region n U η sep) P q X →
        Smooth (Q:=Q) (J:=J) Z M ν (region n U η sep) P q h d):=by
  classical
  intro level shift L
  have box:=legal n U η sep
  obtain ⟨lens,_,B,w,issued,K,kp,openStage⟩:=WilsonPublicForkPublicRows.original F J Z M ν ms fund
    pace V run report positive h
  obtain ⟨E,b,bp,stage⟩:=openStage θ clock n d _ box.1 box.2.1
  refine ⟨lens,E,?_⟩
  intro P q room
  let A:=P+E+1
  obtain ⟨independent,ip,paid⟩:=stage P A (by dsimp [A]; omega) (by dsimp [A]; omega) (by dsimp [A]; omega)
  obtain ⟨γ,γp,entry⟩:=paid q (by dsimp [A]; omega)
  let Vof:=axes (R:=R) d
  let Ready (c:WilsonOrdinaryNestedBasis.Choice G d) (a:Fin n→ℕ) (e:ℕ) (r:ℝ) (x:Names R d h):Prop:=
    ∃tp:0<r/((θ r)^A)^2,wage F J Z L (Vof c) a e r x ∧
    ∀ψ:Test n,tsupport ψ⊆region n U η sep→∀a₁ a₂:ℝ,0≤a₁→0≤a₂→
      Rows F J Z L B w issued A P q (Vof c) r tp x ψ a₁ a₂ →
      ‖(homogeneous F J Z r h).symm (basket Q h (Frame.born (homogeneous F J Z) r (Vof c)) r ψ) -
        prediction R.family d h Z M ν (Vof c) ψ q (θ r)‖ ≤
        (K*(b+a₁+independent+γ*a₂)*(∏i,‖Vof c i‖)*(θ r)^P)*(∫z:Points n,‖ψ z‖)
  have roster(c):∃a e,∃x:ℝ→Names R d h,∀ᶠr in trail,Ready c a e r (x r):=by
    obtain ⟨a,e,credits⟩:=entry (Vof c)
    refine ⟨a,e,scheduled ?_⟩
    filter_upwards [credits] with r ql
    obtain ⟨tp,ins,out,input,output,heard⟩:=ql
    refine ⟨(ins,out),tp,⟨input,output⟩,?_⟩
    intro ψ supp a₁ a₂ h₁ h₂ notes
    exact (heard ψ a₁ a₂ supp h₁ h₂ notes).trans_eq (by unfold Read.Value; ring)
  choose a e x valid using roster
  let X:Panel R d h:=⟨B,w,issued,A,x⟩
  refine ⟨X,rfl,?_,?_⟩
  · intro c
    refine ⟨a c,e c,?_⟩
    filter_upwards [valid c] with r accepted
    exact ⟨accepted.choose,accepted.choose_spec.1⟩
  · intro income c
    obtain ⟨a₁,a₂,h₁,h₂,settled⟩:=income c
    refine ⟨K*(b+a₁+independent+γ*a₂)*(∏i,‖Vof c i‖),by positivity,?_⟩
    filter_upwards [settled,valid c] with r ready accepted ψ support
    exact accepted.choose_spec.2 ψ support a₁ a₂ h₁ h₂ (ready accepted.choose ψ support)
end YM.Integration.WilsonPhysicalDeterminingVertex
end
