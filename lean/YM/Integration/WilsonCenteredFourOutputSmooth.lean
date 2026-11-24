import YM.Integration.WilsonCenteredFourSpatialPublic
import YM.Integration.WilsonCenteredFourOutputDeposit
import YM.Integration.WilsonCenteredFourOutputOperator

/-! The finite independent experiment and the actual smoothed coefficient of the
original two weight-four inputs, on one measured hierarchy and detector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputSmooth
open Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits PhysMS Trace.Pilot Climb
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Theater Trace Trace.Terrace
open RG12 SharpGram OPE.Log PhysicalNext.Repeat.Legato OPE.Levy
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonMacroscopicRichSignedAmplitude WilsonMSDictionaryVector WilsonCenteredFourOutputSensor GapsContact.Seams
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}
    (ms:Main.Match Z simple M σ branch)
local notation "d₄" => (fun _:Fin 2=>4)

theorem original {Y:(Bel R.family.book).Hierarchy}(lead:Leading F J)
    (owed:∀d,∀ᶠr in trail, Frame.obedient F Y (J r) d)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac:Facilities R.family f S){l:Ultrafilter (ℕ×ℕ)}(lo:(l:Filter _)≤f.fuse)
    (bill:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    {arch:Arch R.family}(bliss:Bliss F l arch Y)(V:Store G)(salary:WilsonThermometerWeakPairSector.Salary F Q J)(c:Q.channels 4):
    LogTrace F Q.port ∧
    ∃B:Profiles R 4,∃w:B.probes.index→Atom (R:=R) 4,
    ∃issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid 4 (w j),
    ∃(k:ℕ)(H:ℝ),0≤H ∧ ∀(g:ℝ→ℝ),Coupling G g→
    ∀(K:Set (Points 2)),IsCompact K→K⊆conf 2→∃(E:ℕ)(C:ℝ),0≤C ∧ ∀P A:ℕ,P+E≤A→
    ∀ᶠr in trail, let t:=r/((g r)^A)^2
    ∃ tp:0<t,∀(v:Fin 2→Free R.family 4)(ψ:Test 2),tsupport ψ⊆K→∀(q:ℕ)(D:ℝ),
      let pub:=homogeneous F J Z r
      let u:=fun i=>pub 4 (v i)
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      let observed:=fun j=>appeared F (d:=d₄) u (X j) r ψ
      let bank:=((ms.separatedOPE ν).wilson.light 4).choose
      let value:=fun s=>experiment R.family d₄ 4 Z M ν v ψ bank q (g r) s
      let forecast:=prediction R.family d₄ 4 Z M ν v ψ q (g r)
      let fee:=(∫x:Points 2,‖ψ x‖)*(∏i,‖v i‖)*C+D
      (∃ᶠs:ℝ in atTop,‖observed-(fun j=>(X j).charge F 4 (pub 4 (value s)))‖≤D*g r^(P+A*9))→
      ‖(∫x:Points 2,ψ x*Q.coef 4 c (d:=d₄) (posed r x) u 0)-grade F Q c (pub 4 forecast)‖≤
        H*dock r^k*r^4*fee*(g r)^P:=by
  obtain ⟨logged,B,w,issued,L,l0,read⟩:=WilsonPublicOutputSmooth.original F J Z M ν ms lead owed Q fac lo bill 4
  obtain ⟨k,H,h0,price⟩:=WilsonCenteredFourOutputOperator.paid F Q J (simple:=simple) bliss bill V lead c
  obtain ⟨U,u0,bridge⟩:=WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple 4
  refine ⟨logged,B,w,issued,k,H*U*L,by positivity,?_⟩
  intro g hg K compact spread
  obtain ⟨E,C,c0,spatial⟩:=WilsonCenteredFourSpatialPublic.original F Q J Z V simple lead owed salary fac.toServices B w issued g hg K compact spread
  refine ⟨E,C,c0,?_⟩
  intro P A window
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [read g hg P E A window,price,bridge,spatial A (by omega),WilsonCenteredFourOutputDeposit.original F Q fac.toServices compact spread,self_mem_nhdsWithin,small]
    with r decoder gradeCost transfer space deposited (rp:0<r) small
  dsimp only at decoder space
  obtain ⟨tp,measured⟩:=decoder;refine ⟨tp,?_⟩
  intro v ψ scope q D pub u X observed bank value forecast fee independent
  let C₀:=(∫x:Points 2,‖ψ x‖)*(∏i,‖v i‖)*C
  have mass:0≤∫x:Points 2,‖ψ x‖:=integral_nonneg fun _=>norm_nonneg _
  have cp:0≤C₀:=by dsimp only [C₀];positivity
  have cut:=measured 2 d₄ v ψ q C₀ D cp (space tp v ψ scope) independent
  let phys:=basket Q 4 (d:=d₄) u r ψ
  let d:=(pub 4).symm phys-forecast
  have step: ‖d‖≤L*fee*(g r)^P:=cut.2
  have tested:=gradeCost phys ((J r 4).symm (pub 4 forecast))
  have id:(J r 4).symm phys-(J r 4).symm (pub 4 forecast)=active F J Z r 4 d:=by
    simp only [active,LinearEquiv.trans_apply,d,map_sub,LinearEquiv.apply_symm_apply,pub]
  rw [LinearEquiv.apply_symm_apply,id] at tested
  rw [←deposited u c ψ scope]
  have dock0:0≤dock r:=zero_le_one.trans (dock_valid r ⟨rp,small⟩)
  exact tested.trans ((mul_le_mul_of_nonneg_left ((transfer d).trans (mul_le_mul_of_nonneg_left step u0)) (by positivity)).trans_eq (by ring))

end YM.Integration.WilsonCenteredFourOutputSmooth
