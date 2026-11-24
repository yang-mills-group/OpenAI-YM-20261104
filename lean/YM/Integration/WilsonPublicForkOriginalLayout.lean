import YM.Integration.WilsonPublicForkSmoothBall
import YM.Integration.WilsonCenteredSelectedLayout

/-! The reporting level and frame on the originally selected physical MatrixTicket
pay the actual microscopic incoming and determining columns on all eligible volumes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkOriginalLayout
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

/-- The original inputs and every output basis lift are named and priced before choosing the
inner profile, independent outer cutoff, and either regulator of the Wilson measurement. -/
theorem original {κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (pace:WilsonWindowReportingPace.Slow R.kit)(V:XSpace.Normalize.Store G)
    {course:Almanac F}{Y:(Bel R.family.book).Hierarchy}{U:Ultrafilter (ℕ×ℕ)}{arc:Arch R.family}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}(run:WilsonViewerElectedHierarchy.Selected.{u} F course Q J Y arc U simple cohort)
    (report:ℕ)(positive:0<report)(h:ℕ):
    let level:=WilsonMeasuredWindow.stop R.family.path.levels simple report
    let shift:=fun (d:ℕ) (_:ℝ)=>LinearEquiv.refl ℂ (R.family.label d)
    let L:=WilsonOriginalBlissObserved.layout F run.bliss J level shift
    L.lens=(U:Filter UVIndex) ∧
    LogTrace F Q.port ∧
    ∃ B:Profiles R h, ∃ w:B.probes.index→Atom (R:=R) h,
    ∃ issued:∀ j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
    ∃ K:ℝ, 0≤K ∧ ∀ (g:ℝ→ℝ),Coupling G g → ∀ (n:ℕ) (d:Fin n→ℕ) (box:Set (Points n)),
    IsCompact box → box⊆conf n → ∃ (E:ℕ)(fee:ℝ),0≤fee ∧ ∀ q:ℕ, ∃ gramFee:ℝ,0≤gramFee ∧ ∀ P A:ℕ,0<A → P+E≤A →
    ∀ v:(i:Fin n)→RG17.Free R.family (d i),
    ∃ a:Fin n→ℕ, ∃ c:ℕ, ∀ᶠ r in trail,
    let pub:=homogeneous F J Z r
    let t:=r/((g r)^A)^2
    let β:=R.family.path.levels.clock.hatBeta (L.level r)
    let axis:=WilsonMSDictionaryVector.basis R.family h
    ∃ tp:0<t, ∃ ins:(i:Fin n)→R.family.label (d i), ∃ out:Dframe.Toon G h→R.family.label h,
    (∀ i,(∀ N per:ℕ,level r≤N → Spindle.paid R.family (d i) (level r) N per (atRef L (d i) r (N,per) (ins i))
        ≤β^(a i)*‖(J r (d i)).symm (pub (d i) (v i))‖) ∧
      master L (d i) r (ins i)=pub (d i) (v i)) ∧
    (∀ k,(∀ N per:ℕ,level r≤N → Spindle.paid R.family h (level r) N per (atRef L h r (N,per) (out k))
        ≤β^c*‖(J r h).symm (pub h (axis k))‖) ∧
      master L h r (out k)=pub h (axis k)) ∧
    ∀ (ψ:Test n) (a₁ a₂ a₃:ℝ),tsupport ψ⊆box → 0≤a₁ → 0≤a₂ → 0≤a₃ →
      let amplitude:=(∏i,‖v i‖)*(∫x:Points n,‖ψ x‖)
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      let near:=fun i=>pub (d i) (v i)
      let physical:=RG17.basket Q h (d:=d) near r ψ
      let bank:=((ms.separatedOPE ν).wilson.light h).choose
      let issuedMS:=fun s=>experiment R.family d h Z M ν v ψ bank q (g r) s
      let D:=fee+a₁+a₃+gramFee*a₂
      let η:=(g r)^(P+A*(2*h+1))
      ∀ (ordinary:ℝ → UVIndex → B.probes.index → ℂ)
        (gram:ℝ → UVIndex → Dframe.Toon G h → B.probes.index → ℂ),
      (∃ᶠ s:ℝ in atTop, f.late fun N per=>
        (∀j,‖packMark L (X j) d ins r ψ (N,per)-ordinary s (N,per) j‖≤(a₁*amplitude)*η) ∧
        (∀k j,‖headMark L (X j) h r (N,per) (out k)-gram s (N,per) k j‖≤a₂*η) ∧
        ∀j,‖ordinary s (N,per) j-∑k,axis.repr (issuedMS s) k*gram s (N,per) k j‖≤(a₃*amplitude)*η) →
      ‖(pub h).symm physical-prediction R.family d h Z M ν v ψ q (g r)‖ ≤ K*D*amplitude*(g r)^P := by
  let level:=WilsonMeasuredWindow.stop R.family.path.levels simple report
  let shift:=fun (d:ℕ) (_:ℝ)=>LinearEquiv.refl ℂ (R.family.label d)
  let L:=WilsonOriginalBlissObserved.layout F run.bliss J level shift
  obtain ⟨same,fees,_⟩:=WilsonCenteredSelectedLayout.original F J fund pace run report positive
  have grow:Tendsto L.level trail atTop:=WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple report positive
  obtain ⟨logged,B,w,issued,K,kp,read⟩:=WilsonPublicForkSmoothBall.original F J Z M ν ms fund course run.phases V
    run.leading run.obeys Q run.foundation run.facilities run.bliss run.matrix L grow fees h
  refine ⟨same,logged,B,w,issued,K,kp,?_⟩
  intro g hg n d box compact spread
  obtain ⟨E,fee,fp,budget⟩:=read g hg n d box compact spread
  refine ⟨E,fee,fp,?_⟩
  intro q
  obtain ⟨gramFee,op,physics⟩:=budget q
  refine ⟨gramFee,op,?_⟩
  intro P A ap threshold v
  obtain ⟨a,c,hire⟩:=physics P A ap threshold v
  refine ⟨a,c,?_⟩
  have levels:∀ᶠr in trail,∀i:Fin n,R.family.ref (d i)≤L.level r:=
    eventually_all.mpr fun i=>grow.eventually_ge_atTop (R.family.ref (d i))
  filter_upwards [hire,levels,grow.eventually_ge_atTop (R.family.ref h)] with r sold birth output
  dsimp only at sold ⊢
  obtain ⟨tp,ins,out,invoices,axes,measured⟩:=sold
  refine ⟨tp,ins,out,fun i=>⟨?_,(invoices i).2⟩,fun k=>⟨?_,(axes k).2⟩,measured⟩
  · intro N per later
    exact (WilsonReportRegulatedSmear.reference (p:=per) L r (d i) (ins i) (birth i) later).le.trans (invoices i).1
  · intro N per later
    exact (WilsonReportRegulatedSmear.reference (p:=per) L r h (out k) output later).le.trans (axes k).1

end YM.Integration.WilsonPublicForkOriginalLayout
