import YM.Integration.WilsonPublicForkCharge
import YM.Integration.WilsonPublicOutputSmooth

/-! A selected finite family of literal physical inputs and the full measured
output, in the original order, on the matrix ticket of the original extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkPanel
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
      ‖(fun j=>(X j).charge F h (basket Q h (d:=d) u r ψ)) -
        (fun j=>appeared F (d:=d) u (X j) r ψ)‖ ≤
        ((∫x:Points n,‖ψ x‖)*(∏i,‖v i‖)*C)*(((g r)^A)^2)^(h+1)/(g r)^E:=by
  let φ:=fun j=>profile (B.probes.shell j) (w j) (issued j) (test B j)
  let b:=fun j=>(Bel R.family.book).project h (w j)
  choose D C c0 pay using fun j=>WilsonPublicForkCharge.original F fund L done' fac bliss ticket Q book J V lead g hg d h h K compact spread (φ j)
  choose Lₙ pn near using fun i=>WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple (d i)
  obtain ⟨Lₒ,po,far⟩:=WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple h
  let E:=∑j,D j
  let W:=fun j=>(∫z:Points 2,‖φ j z‖)*C j*(∏i,Lₙ i)*(Lₒ*‖b j‖)
  have lp:0≤∏i,Lₙ i:=Finset.prod_nonneg fun i _=>(pn i)
  have W0(j):0≤W j:=by dsimp only [W];have:=c0 j;positivity
  refine ⟨E,∑j,W j,Finset.sum_nonneg (fun j _=>W0 j),?_⟩
  intro A ap
  have all:=eventually_all.mpr (fun j=>pay j (A*2) (by omega))
  filter_upwards [all,eventually_all.mpr near,(small simple g hg (A*2)).eventually far,hg.positive,
     (hg.conforms simple).eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin]
    with r paid nr fr gp g1 (rp:0<r)
  dsimp only;intro tp v ψ inside
  let t:=r/((g r)^A)^2
  have clock:scale g (A*2) r=t:=by rw [scale,pow_mul]
  rw [clock] at fr
  let y:=fun i=>active F J Z r (d i) (v i)
  let u:=fun i=>homogeneous F J Z r (d i) (v i)
  have placed:(fun i=>J r (d i) (y i))=u:=by funext i;simp [y,u,active,LinearEquiv.trans_apply]
  have vu:(∏i,‖y i‖)≤(∏i,Lₙ i)*(∏i,‖v i‖):=by
    rw [←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>nr i (v i))
  let mass:=∫x:Points n,‖ψ x‖
  have m0:0 ≤ mass:=integral_nonneg fun _=>norm_nonneg _
  have v0:0≤∏i,‖v i‖:=Finset.prod_nonneg fun _ _=>norm_nonneg _
  have tot:0≤∑j,W j:=Finset.sum_nonneg (fun j (_:j∈Finset.univ)=>W0 j)
  have ratio:r/t=((g r)^A)^2:=by dsimp [t];field_simp [rp.ne',gp.ne']
  have ratio0:0≤(r/t)^(h+1):=pow_nonneg (div_nonneg rp.le tp.le) _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have atj:=paid j;rw [clock] at atj
  have actual:=atj tp y (active F J Z t h (b j)) ψ inside
  change ‖appeared F (d:=d) (fun i=>J r (d i) (y i)) _ r ψ-External.charge F _ h (basket Q h (d:=d) (fun i=>J r (d i) (y i)) r ψ)‖≤_ at actual
  rw [placed] at actual
  change ‖External.charge F _ h (basket Q h (d:=d) u r ψ)-appeared F (d:=d) u _ r ψ‖≤_
  rw [norm_sub_rev]
  have mj:0≤∫z:Points 2,‖φ j z‖:=integral_nonneg fun _=>norm_nonneg _
  have dj:D j≤E:=Finset.single_le_sum (f:=D) (fun k _=>Nat.zero_le _) (Finset.mem_univ j)
  have priced:(r/t)^(h+1)/g r^(D j)≤(r/t)^(h+1)/g r^E:=
    div_le_div_of_nonneg_left ratio0 (pow_pos gp _) (pow_le_pow_of_le_one gp.le g1 dj)
  calc
    _≤ mass*((∫z:Points 2,‖φ j z‖)*(C j*(∏i,‖y i‖)*‖active F J Z t h (b j)‖*((r/t)^(h+1)/g r^(D j)))):=actual
    _≤ mass*((∫z:Points 2,‖φ j z‖)*(C j*((∏i,Lₙ i)*(∏i,‖v i‖))*(Lₒ*‖b j‖)*((r/t)^(h+1)/g r^E))):=by
      have cp:=c0 j
      gcongr;first | exact cp | exact vu | exact fr (b j)
    _=(mass*(∏i,‖v i‖)*W j)*(r/t)^(h+1)/g r^E:=by dsimp only [W];ring
    _≤(mass*(∏i,‖v i‖)*(∑i,W i))*(r/t)^(h+1)/g r^E:=by
      gcongr;exact Finset.single_le_sum (fun i (_:i∈Finset.univ)=>W0 i) (Finset.mem_univ j)
    _=_:=by rw [ratio]
end YM.Integration.WilsonPublicForkPanel
