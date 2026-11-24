import YM.Integration.WilsonPublicForkTwoHearings

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkPublicRows
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

/-- The original moving exterior uses this fixed full public direction on its own date. -/
def probe {h:ℕ}(B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)(j:B.probes.index):RG17.Free R.family h:=
  (Bel R.family.book).project h (w j)

theorem placed {h:ℕ}(B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
    {t:ℝ}(tp:0<t)(j:B.probes.index):
    WilsonPublicOutputSmooth.exterior F J Z B w issued tp j=
      WilsonMacroscopicRichSignedAmplitude.stencil J (profile (B.probes.shell j) (w j) (issued j) (test B j)) tp
        ⟨h,WilsonMacroscopicRichTwoDatePivot.active F J Z t h (probe B w j)⟩:=rfl

include ms
/-- The two finite signed measurements use the original pivot’s full public labels in both
tables. All geometric and profile prices are fixed before the input profile. -/
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
    IsCompact box → box⊆conf n → ∃ (E:ℕ)(fee:ℝ),0≤fee ∧ ∀P A:ℕ,0<A → P+E≤A → P<A →
    ∃ independentFee:ℝ,0≤ independentFee ∧ ∀q:ℕ,P+A*(2*h+1)<q+1 →
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
          WilsonPublicForkIndependentFields.full R.family d h Z q (g r) s v (probe B w j) ψ (φ j)‖≤(a₁*amplitude)*η) ∧
        (∀k j,‖headMark L (X j) h r (N,per) (out k)-
          WilsonPublicForkIndependentFields.gram R.family h Z q (g r) s (probe B w j) (φ j) k‖≤a₂*η)) →
      ‖(pub h).symm physical-prediction R.family d h Z M ν v ψ q (g r)‖≤
        K*(fee+a₁+independentFee+gramFee*a₂)*amplitude*(g r)^P := by
  obtain ⟨layout,log,B,w,issued,K,kp,read⟩:=WilsonPublicForkTwoHearings.original F J Z M ν ms fund pace
    V run report positive h
  refine ⟨layout,log,B,w,issued,K,kp,?_⟩
  intro g hg n d box compact clear
  obtain ⟨E,fee,fp,bought⟩:=read g hg n d box compact clear
  refine ⟨E,fee,fp,?_⟩
  intro P A ap wage margin
  let c:=∑j,‖probe B w j‖
  have cp:0≤c:=Finset.sum_nonneg fun j _=>norm_nonneg _
  have paid:∀ᶠr in trail,∀j,‖probe B w j‖*(g r)^0≤c:=Eventually.of_forall fun r j=>by
    rw [pow_zero,mul_one]
    exact Finset.single_le_sum (fun i _=>norm_nonneg (probe B w i)) (Finset.mem_univ _)
  simpa only [Nat.add_zero] using bought P A 0 ap wage (by omega) (fun _ j=>probe B w j) c cp paid

end YM.Integration.WilsonPublicForkPublicRows
