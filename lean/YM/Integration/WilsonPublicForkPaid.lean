import YM.Integration.WilsonPublicForkPanel
import YM.Integration.WilsonPublicForkAdmissible

/-! A selected finite family of literal physical inputs and the full measured
output, in the original order, on the matrix ticket of the original extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkPaid
open Function Finset Filter Set Table Spec Climb OPE OPE.Orbits OPE.Prescription OPE.Log EveryPhase OPE.Nesting
open Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact GapsContact.Ascent GapsContact.Seams
open OPE.Levy Extraction Maxwell XSpace XSpace.Normalize Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open Next.UVStress Trace.Terrace WilsonPublicForkLabels WilsonThermometerWeakPairClock
open YM.Integration.WilsonLimitConstruction
open MeasureTheory WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichTwoDatePivot
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale Pert Pert.Position MS MS.Local.Physical
open MS.Menus MS.Land MS.Theater RegulatorIR.FVAAlt2.Lodge Extra.FD
open scoped Classical Topology BigOperators
universe u
variable {G:Gauge}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}
  {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)

theorem original {simple:G.Simple}{κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (L:Almanac F)(done':Completed F L)(fac:Facilities R.family f S)
    {𝓛:Ultrafilter (ℕ×ℕ)}{arc:Arch R.family}{Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arc Y)(ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(book:Foundation F Q)
    (J:ℝ → tower S)(V:Store G)(lead:Leading F J)(Z:WilsonPrescription G)
    (owed:∀d,∀ᶠt in trail,Frame.obedient F Y (J t) d)
    {n:ℕ}(d:Fin n → ℕ)(h:ℕ)(B:Profiles R h)(w:B.probes.index → Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
    (g:ℝ → ℝ)(hg:Coupling G g)(K:Set (Points n))(compact:IsCompact K)(spread:K⊆conf n):
    ∃(E:ℕ)(C:ℝ),0≤C ∧ ∀A:ℕ,0<A → ∀ᶠ r in trail,let t:=r/((g r)^A)^2
      ∀(tp:0<t)(v:∀i,RG17.Free R.family (d i))(ψ:Test n),tsupport ψ⊆K →
      let u:=fun i=>homogeneous F J Z r (d i) (v i)
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      (∀j,packs (X j) r ψ) ∧
      (∀j,Integrable (fun z:Points ((X j).n+1)=>(X j).test z*query F u ((X j).offset z) (X j).labels none r ψ)) ∧
      ‖(fun j=>(X j).charge F h (basket Q h (d:=d) u r ψ)) -
        (fun j=>appeared F (d:=d) u (X j) r ψ)‖ ≤
        ((∫x:Points n,‖ψ x‖)*(∏i,‖v i‖)*C)*(((g r)^A)^2)^(h+1)/(g r)^E:=by
  obtain ⟨E,C,cp,paid⟩:=WilsonPublicForkPanel.original F fund L done' fac bliss ticket Q book J V lead Z owed
    d h B w issued g hg K compact spread
  let φ:=fun j=>profile (B.probes.shell j) (w j) (issued j) (test B j)
  choose M δ η mn dp ep room using fun j=>WilsonPublicForkSupport.original K compact spread (φ j)
  refine ⟨E,C,cp,fun A ap=>?_⟩
  have small:Tendsto (fun r=>(g r^A)^2) trail (𝓝 (0:ℝ)):=by
    simpa [zero_pow ap.ne'] using ((hg.conforms simple).pow A).pow 2
  have nm:=eventually_all.mpr (fun j=>small.eventually (ge_mem_nhds (ep j)))
  filter_upwards [paid A ap,nm,hg.positive,self_mem_nhdsWithin] with r physical fits gp (rp:0<r)
  dsimp only;intro tp v ψ inside
  let t:=r/((g r)^A)^2
  let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
  let u:=fun i=>homogeneous F J Z r (d i) (v i)
  have eq:r/t=((g r)^A)^2:=by dsimp [t];field_simp [rp.ne',gp.ne']
  have admissible(j):packs (X j) r ψ:=WilsonPublicForkAdmissible.covered J (φ j) tp _ ψ
    (fun x hx z hz=>(room j r t rp tp (eq.trans_le (fits j)) x (inside hx) z hz).2.2.2.2.1)
  exact ⟨admissible,fun j=>WilsonPublicForkAdmissible.integrable F (X j) r u ψ (admissible j),physical tp v ψ inside⟩
end YM.Integration.WilsonPublicForkPaid
