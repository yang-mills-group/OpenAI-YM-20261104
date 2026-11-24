import YM.Integration.WilsonPublicForkIndependentPanel
import YM.Integration.WilsonPublicForkSmoothBall
import YM.Integration.WilsonCenteredSelectedLayout

/-! The complete normalized output is priced by just the separately signed original
ordinary product and the original two-point basis on the chosen physical frame. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkTwoHearings
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

include ms
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
    IsCompact box → box⊆conf n → ∃ (E:ℕ)(fee:ℝ),0≤fee ∧ ∀P A e:ℕ,0<A → P+E≤A → P+e<A →
    ∀(farField:ℝ→B.probes.index→RG17.Free R.family h)(c₀:ℝ),0≤c₀ →
    (∀ᶠr in trail,∀j,‖farField r j‖*(g r)^e≤c₀) →
    ∃ independentFee:ℝ,0≤ independentFee ∧ ∀q:ℕ,P+e+A*(2*h+1)<q+1 →
    ∃ gramFee:ℝ,0≤gramFee ∧ ∀ v:(i:Fin n)→RG17.Free R.family (d i),
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
    ∀ (ψ:Test n) (a₁ a₂:ℝ),tsupport ψ⊆box → 0≤a₁ → 0≤a₂ →
      let amplitude:=(∏i,‖v i‖)*Read.Value ψ
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      let φ:=fun j=>profile (B.probes.shell j) (w j) (issued j) (test B j)
      let s:=WilsonPublicForkIndependentPlacement.age A (g r)
      let physical:=RG17.basket Q h (d:=d) (fun i=>pub (d i) (v i)) r ψ
      let η:=(g r)^(P+A*(2*h+1))
      (f.late fun N per=>
        (∀j,‖packMark L (X j) d ins r ψ (N,per)-
          WilsonPublicForkIndependentFields.full R.family d h Z q (g r) s v (farField r j) ψ (φ j)‖≤(a₁*amplitude)*η) ∧
        (∀k j,‖headMark L (X j) h r (N,per) (out k)-
          WilsonPublicForkIndependentFields.gram R.family h Z q (g r) s (farField r j) (φ j) k‖≤a₂*η)) →
      ‖(pub h).symm physical-prediction R.family d h Z M ν v ψ q (g r)‖≤
        K*(fee+a₁+independentFee+gramFee*a₂)*amplitude*(g r)^P:=by
  let level:=WilsonMeasuredWindow.stop R.family.path.levels simple report
  let shift:=fun (d:ℕ) (_:ℝ)=>LinearEquiv.refl ℂ (R.family.label d)
  let L:=WilsonOriginalBlissObserved.layout F run.bliss J level shift
  obtain ⟨same,fees,_⟩:=WilsonCenteredSelectedLayout.original F J fund pace run report positive
  have grow:Tendsto L.level trail atTop:=WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple report positive
  obtain ⟨logged,B,w,issued,K,kp,read⟩:=WilsonPublicForkRelease.original F J Z M ν ms fund course run.phases V
    run.leading run.obeys Q run.foundation run.facilities run.bliss run.matrix L grow fees h
  refine ⟨same,logged,B,w,issued,K,kp,?_⟩
  intro g hg n d box compact spread
  obtain ⟨E,fee,fp,physical⟩:=read g hg n d box compact spread
  refine ⟨E,fee,fp,?_⟩
  intro P A e ap enough reserve farField c₀ c₀p farPaid
  let φ:=fun j=>profile (B.probes.shell j) (w j) (issued j) (test B j)
  obtain ⟨independentFee,ip,far⟩:=WilsonPublicForkIndependentPanel.original R.family d h Z M ν ms g hg box compact
    spread φ farField e c₀ c₀p farPaid
  refine ⟨independentFee,ip,?_⟩
  intro q order
  obtain ⟨gramFee,op,invest⟩:=WilsonPublicForkTestFee.inversion R.family d h Z M ν ms box compact spread q
  refine ⟨gramFee,op,?_⟩
  intro v
  obtain ⟨a,c,hires⟩:=physical P A ap enough v
  refine ⟨a,c,?_⟩
  have levels:∀ᶠr in trail,∀i:Fin n,R.family.ref (d i)≤L.level r:=
    eventually_all.mpr fun i=>grow.eventually_ge_atTop (R.family.ref (d i))
  filter_upwards [hires,levels,grow.eventually_ge_atTop (R.family.ref h),far q P A reserve order,
    hg.positive,(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one)]
    with r hires birth output far_ok gp one
  dsimp only at hires ⊢
  obtain ⟨tp,ins,out,invoices,axes,hear⟩:=hires
  refine ⟨tp,ins,out,fun i=>⟨?_,(invoices i).2⟩,fun k=>⟨?_,(axes k).2⟩,?_⟩
  · intro N per later
    exact (WilsonReportRegulatedSmear.reference (p:=per) L r (d i) (ins i) (birth i) later).le.trans (invoices i).1
  · intro N per later
    exact (WilsonReportRegulatedSmear.reference (p:=per) L r h (out k) output later).le.trans (axes k).1
  intro ψ a₁ a₂ allowed pa pb signed
  let amplitude:=(∏i,‖v i‖)*Read.Value ψ
  have pos:0≤amplitude:=mul_nonneg (Finset.prod_nonneg fun _ _=>norm_nonneg _) (Read.value_0 _)
  let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
  let age:=WilsonPublicForkIndependentPlacement.age A (g r)
  let joint:=fun j=>WilsonPublicForkIndependentFields.full R.family d h Z q (g r) age v (farField r j) ψ (φ j)
  let two:=fun k j=>WilsonPublicForkIndependentFields.gram R.family h Z q (g r) age (farField r j) (φ j) k
  let bank:=((ms.separatedOPE ν).wilson.light h).choose
  let e_s:=experiment R.family d h Z M ν v ψ bank q (g r)
  let y:=prediction R.family d h Z M ν v ψ q (g r)
  have lim_e:Tendsto e_s atTop (𝓝 y):=experiment_limit R.family d h Z M ν v ψ ms bank
    ((ms.separatedOPE ν).wilson.light h).choose_spec.2 q (g r)
  let η:=(g r)^(P+A*(2*h+1))
  let C:=(Read.Value ψ)*(∏i,‖v i‖)*fee
  let rhs:=fun δ:ℝ=>K*(C+(a₁*amplitude+(independentFee*amplitude+δ)+(gramFee*amplitude+δ)*a₂))*(g r)^P
  have cont:Continuous rhs:=by dsimp only [rhs];fun_prop
  have each(δ:ℝ)(dp:0<δ):
      ‖((homogeneous F J Z r) h).symm (RG17.basket Q h (d:=d) (fun i=>homogeneous F J Z r (d i) (v i)) r ψ)-y‖≤rhs δ:=by
    have edits:=WilsonPublicForkIndependentReceipts.original e_s y lim_e
      (fun N per j=>packMark L (X j) d ins r ψ (N,per)) (fun N per k j=>headMark L (X j) h r (N,per) (out k))
      joint two (a:=a₁*amplitude) (b:=a₂) (c:=independentFee*amplitude) (η:=η)
      (pow_pos gp _) signed (far_ok v ψ allowed) δ dp
    have cash:=invest v ψ allowed (g r) ⟨by linarith,one⟩ δ dp
    have receipt:=WilsonPublicForkReadings.ordered F L X d h ψ ins out r e_s
      (add_nonneg (mul_nonneg op pos) dp.le) (by simpa only [amplitude,Read.Value,mul_assoc] using cash)
      (a₁*amplitude) a₂ (independentFee*amplitude+δ) η (mul_nonneg pa pos) pb (add_nonneg (mul_nonneg ip pos) dp.le)
      (pow_nonneg gp.le _) (fun _ _=>joint) (fun _ _=>two) edits
    exact (hear ψ q _ allowed receipt).2
  have lim:Tendsto rhs (𝓝[>] 0) (𝓝 (rhs 0)):=(cont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact (ge_of_tendsto lim ((show ∀ᶠδ:ℝ in 𝓝[>] 0,0<δ from self_mem_nhdsWithin).mono
    (fun δ dp=>each δ dp))).trans_eq (by dsimp only [rhs,C,amplitude];ring)

end YM.Integration.WilsonPublicForkTwoHearings
