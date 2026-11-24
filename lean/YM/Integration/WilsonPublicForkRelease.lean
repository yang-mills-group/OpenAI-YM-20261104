import YM.Integration.WilsonPublicForkPaid
import YM.Integration.WilsonPublicOutputPhysical

/-! The true moving spatial estimate and the signed finite arrays reconstruct
the complete positive output on a single original physical extraction. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkRelease
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
    (course:Almanac F)(done':Completed F course)(V:XSpace.Normalize.Store G)
    {Y:(Bel R.family.book).Hierarchy} (lead:Leading F J)
    (owed:∀ d,∀ᶠ r in trail,Frame.obedient F Y (J r) d)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (book:Foundation F Q)(fac:Facilities R.family f S) {U:Ultrafilter (ℕ×ℕ)} {arc:Arch R.family} (bliss:Bliss F U arc Y)
    (ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (U:Filter _)) (L:Layout F)
    (growing:Tendsto L.level trail atTop)
    (fees:∀ h, Pier.Lair.Paying F (Pier.Lair.tender F L J) h) (h:ℕ) :
    LogTrace F Q.port ∧
    ∃ B:Profiles R h, ∃ w:B.probes.index→Atom (R:=R) h,
    ∃ issued:∀ j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
    ∃ K:ℝ, 0≤K ∧ ∀ (g:ℝ→ℝ),Coupling G g → ∀ (n:ℕ) (d:Fin n→ℕ) (box:Set (Points n)),
    IsCompact box → box⊆conf n → ∃ (E:ℕ)(fee:ℝ),0≤fee ∧ ∀ P A:ℕ,0<A → P+E≤A →
    ∀ v:(i:Fin n)→RG17.Free R.family (d i),
    ∃ a:Fin n→ℕ, ∃ c:ℕ, ∀ᶠ r in trail,
    let pub:=homogeneous F J Z r
    let t:=r/((g r)^A)^2
    let β:=R.family.path.levels.clock.hatBeta (L.level r)
    let axis:=WilsonMSDictionaryVector.basis R.family h
    ∃ tp:0<t, ∃ ins:(i:Fin n)→R.family.label (d i), ∃ out:Dframe.Toon G h→R.family.label h,
    (∀ i,mass R.family (d i) (L.shift (d i) r (ins i)) ≤ β^(a i)*‖(J r (d i)).symm (pub (d i) (v i))‖ ∧
      master L (d i) r (ins i)=pub (d i) (v i)) ∧
    (∀ k,mass R.family h (L.shift h r (out k)) ≤ β^c*‖(J r h).symm (pub h (axis k))‖ ∧
      master L h r (out k)=pub h (axis k)) ∧
    ∀ (ψ:Test n) (q:ℕ) (D:ℝ),tsupport ψ⊆box →
      let C:=(∫x:Points n,‖ψ x‖)*(∏i,‖v i‖)*fee
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      let near:=fun i=>pub (d i) (v i)
      let physical:=RG17.basket Q h (d:=d) near r ψ
      let bank:=((ms.separatedOPE ν).wilson.light h).choose
      let issuedMS:=fun s=>experiment R.family d h Z M ν v ψ bank q (g r) s
      (∃ᶠ s:ℝ in atTop, f.late fun N per=>
        ‖contrast F L X d ins out r ψ (issuedMS s) (N,per)‖ ≤ D*(g r)^(P+A*(2*h+1))) →
      (∃ᶠ s:ℝ in atTop, ‖(pub h).symm physical-issuedMS s‖ ≤ K*(C+D)*(g r)^P) ∧
      ‖(pub h).symm physical-prediction R.family d h Z M ν v ψ q (g r)‖ ≤ K*(C+D)*(g r)^P := by
  obtain ⟨logged,B,w,issued,K,kp,read⟩:=WilsonPublicOutputPhysical.original F J Z M ν ms lead owed Q fac bliss.lies ticket
    L growing fees h
  refine ⟨logged,B,w,issued,K,kp,?_⟩
  intro g hg n d box compact spread
  obtain ⟨E,fee,fp,physical⟩:=WilsonPublicForkPaid.original F fund course done' fac bliss ticket Q book J V lead Z owed
    d h B w issued g hg box compact spread
  refine ⟨E,fee,fp,?_⟩
  intro P A ap clock v
  obtain ⟨a,c,returned⟩:=read g hg P E A clock n d v
  refine ⟨a,c,?_⟩
  filter_upwards [returned,physical A ap] with r hire spatial
  dsimp only at hire ⊢
  obtain ⟨tp,ins,out,invoices,heads,hear⟩:=hire
  refine ⟨tp,ins,out,invoices,heads,?_⟩
  intro ψ q D inside
  obtain ⟨packed,integrable,remainder⟩:=spatial tp v ψ inside
  have cost:0≤(∫x:Points n,‖ψ x‖)*(∏i,‖v i‖)*fee:=mul_nonneg
    (mul_nonneg (integral_nonneg fun _=>norm_nonneg _) (Finset.prod_nonneg fun _ _=>norm_nonneg _)) fp
  exact hear ψ q _ D cost packed integrable remainder

end YM.Integration.WilsonPublicForkRelease
