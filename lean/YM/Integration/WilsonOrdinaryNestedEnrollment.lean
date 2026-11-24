import YM.Integration.WilsonOrdinaryNestedSmoothTree
import YM.Integration.WilsonPublicForkOriginalLayout

/-! Original before-test Spindle enrollment for each comparable vertex on the selected physical hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedEnrollment
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
abbrev Names (R:Run G) (d:Fin n→ℕ) (h:ℕ):= ((i:Fin n)→R.family.label (d i)) ×
    (Dframe.Toon G h→R.family.label h)

structure Panel (R:Run G) (d:Fin n→ℕ) (h:ℕ) where
  B:Profiles R h
  w:B.probes.index→Atom (R:=R) h
  issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j)
  rise:ℕ
  labels:WilsonOrdinaryNestedBasis.Choice G d→ℝ→Names R d h

def wage (L:Layout F) (v:∀i,Free R.family (d i)) (a:Fin n→ℕ) (e:ℕ) (r:ℝ) (names:Names R d h):Prop:=
  let pub:=homogeneous F J Z r
  let β:=R.family.path.levels.clock.hatBeta (L.level r)
  let axis:=WilsonMSDictionaryVector.basis R.family h
  (∀i,(∀N per,L.level r≤N→Spindle.paid R.family (d i) (L.level r) N per
    (atRef L (d i) r (N,per) (names.1 i))≤β^(a i)*‖(J r (d i)).symm (pub (d i) (v i))‖) ∧
    master L (d i) r (names.1 i)=pub (d i) (v i)) ∧
  (∀k,(∀N per,L.level r≤N→Spindle.paid R.family h (L.level r) N per
    (atRef L h r (N,per) (names.2 k))≤β^e*‖(J r h).symm (pub h (axis k))‖) ∧
    master L h r (names.2 k)=pub h (axis k))

def signed (L:Layout F) (B:Profiles R h) (w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
    (A P q:ℕ) (v:∀i,Free R.family (d i)) (r:ℝ) (tp:0<r/((θ r)^A)^2) (names:Names R d h)
    (ψ:Test n) (a₁ a₂ a₃:ℝ):Prop:=
  let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
  let axis:=WilsonMSDictionaryVector.basis R.family h
  let bank:=((ms.separatedOPE ν).wilson.light h).choose
  let amp:=(∏i,‖v i‖)*(∫x:Points n,‖ψ x‖)
  let emitted:=fun s=>experiment R.family d h Z M ν v ψ bank q (θ r) s
  let toll:=(θ r)^(P+A*(2*h+1))
  ∃ord:ℝ→UVIndex→B.probes.index→ℂ, ∃gram:ℝ→UVIndex→Dframe.Toon G h→B.probes.index→ℂ,
    ∃ᶠs:ℝ in atTop,f.late fun N per=>
      (∀j,‖packMark L (X j) d names.1 r ψ (N,per)-ord s (N,per) j‖≤(a₁*amp)*toll) ∧
      (∀k j,‖headMark L (X j) h r (N,per) (names.2 k)-gram s (N,per) k j‖≤a₂*toll) ∧
      ∀j,‖ord s (N,per) j-∑k,axis.repr (emitted s) k*gram s (N,per) k j‖≤(a₃*amp)*toll

def Income (L:Layout F) (K:Set (Points n)) (P q:ℕ) (X:Panel R d h):Prop:=
  ∀c,∃a₁ a₂ a₃:ℝ,0≤a₁ ∧ 0≤a₂ ∧ 0≤a₃ ∧ ∀ᶠr in trail,
    ∀tp:0<r/((θ r)^X.rise)^2,∀ψ:Test n,tsupport ψ⊆K→
      signed F J Z M ν ms L X.B X.w X.issued X.rise P q (axes (R:=R) d c) r tp (X.labels c r) ψ a₁ a₂ a₃

private theorem scheduled {T:Type*} [Nonempty T] {D:ℝ→T→Prop} (h:∀ᶠr in trail,∃u,D r u):
    ∃a:ℝ→T,∀ᶠr in trail,D r (a r):=by
  classical
  refine ⟨fun r=>if good:∃u,D r u then good.choose else Classical.choice (inferInstance:Nonempty T),?_⟩
  filter_upwards [h] with r good
  simpa only [dif_pos good] using good.choose_spec

theorem original {κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (pace:WilsonWindowReportingPace.Slow R.kit)(V:XSpace.Normalize.Store G)
    {course:Almanac F}{Y:(Bel R.family.book).Hierarchy}{U0:Ultrafilter (ℕ×ℕ)}{arc:Arch R.family}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}(run:Selected.{u} F course Q J Y arc U0 simple cohort)
    (report:ℕ)(positive:0<report)(clock:Coupling G θ)(d:Fin n→ℕ)(h:ℕ)(U η:ℝ)(sep:0<η):
    let level:=WilsonMeasuredWindow.stop R.family.path.levels simple report
    let shift:=fun (d:ℕ) (_:ℝ)=>LinearEquiv.refl ℂ (R.family.label d)
    let L:=WilsonOriginalBlissObserved.layout F run.bliss J level shift
    L.lens=(U0:Filter UVIndex) ∧ ∃E:ℕ,∀P q,∃X:Panel R d h,
      X.rise=P+E+1 ∧
      (∀c,∃a e,∀ᶠr in trail,0<r/((θ r)^X.rise)^2 ∧
        wage F J Z L (axes (R:=R) d c) a e r (X.labels c r)) ∧
      (Income F J Z M ν ms L (region n U η sep) P q X →
        Smooth (Q:=Q) (J:=J) Z M ν (region n U η sep) P q h d):=by
  classical
  intro level shift L
  have box:=legal n U η sep
  obtain ⟨lens,_,B,w,issued,K,kp,openStage⟩:=WilsonPublicForkOriginalLayout.original F J Z M ν ms fund
    pace V run report positive h
  obtain ⟨E,b,bp,stage⟩:=openStage θ clock n d _ box.1 box.2.1
  refine ⟨lens,E,?_⟩
  intro P q
  obtain ⟨γ,γp,entry⟩:=stage q
  let A:=P+E+1
  let Vof:=axes (R:=R) d
  let Ready (c:WilsonOrdinaryNestedBasis.Choice G d) (a:Fin n→ℕ) (e:ℕ) (r:ℝ) (x:Names R d h):Prop:=
    ∃tp:0<r/((θ r)^A)^2,wage F J Z L (Vof c) a e r x ∧
    ∀ψ:Test n,tsupport ψ⊆region n U η sep→∀a₁ a₂ a₃:ℝ,0≤a₁→0≤a₂→0≤a₃→
      signed F J Z M ν ms L B w issued A P q (Vof c) r tp x ψ a₁ a₂ a₃ →
      ‖(homogeneous F J Z r h).symm (basket Q h (Frame.born (homogeneous F J Z) r (Vof c)) r ψ) -
        prediction R.family d h Z M ν (Vof c) ψ q (θ r)‖ ≤
        (K*(b+a₁+a₃+γ*a₂)*(∏i,‖Vof c i‖)*(θ r)^P)*(∫z:Points n,‖ψ z‖)
  have roster(c):∃a e,∃x:ℝ→Names R d h,∀ᶠr in trail,Ready c a e r (x r):=by
    obtain ⟨a,e,credits⟩:=entry P A (by dsimp [A];omega) (by dsimp [A];omega) (Vof c)
    refine ⟨a,e,scheduled ?_⟩
    filter_upwards [credits] with r ql
    obtain ⟨tp,ins,out,input,output,heard⟩:=ql
    refine ⟨(ins,out),tp,⟨input,output⟩,?_⟩
    intro ψ supp a₁ a₂ a₃ h₁ h₂ h₃ notes
    obtain ⟨ord,gram,money⟩:=notes
    exact (heard ψ a₁ a₂ a₃ supp h₁ h₂ h₃ ord gram money).trans_eq (by ring)
  choose a e x valid using roster
  let X:Panel R d h:=⟨B,w,issued,A,x⟩
  refine ⟨X,rfl,?_,?_⟩
  · intro c
    refine ⟨a c,e c,?_⟩
    filter_upwards [valid c] with r accepted
    exact ⟨accepted.choose,accepted.choose_spec.1⟩
  · intro income c
    obtain ⟨a₁,a₂,a₃,h₁,h₂,h₃,settled⟩:=income c
    refine ⟨K*(b+a₁+a₃+γ*a₂)*(∏i,‖Vof c i‖),by positivity,?_⟩
    filter_upwards [settled,valid c] with r ready accepted ψ support
    exact accepted.choose_spec.2 ψ support a₁ a₂ a₃ h₁ h₂ h₃ (ready accepted.choose ψ support)
end YM.Integration.WilsonOrdinaryNestedEnrollment
end
