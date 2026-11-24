import YM.Integration.WilsonCenteredFourPublicForecast
import YM.Integration.WilsonCenteredFourOutputTreePrice

/-! The genuinely measured positive four-field branch of the original two-vertex
tree. The child detector and the parent evaluate at their own running coupling.
The other grades are removed by their full original branch subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputSmoothTree
open Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits PhysMS Trace.Pilot Climb
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Theater Trace Trace.Terrace
open RG12 SharpGram OPE.Log PhysicalNext.Repeat.Legato OPE.Levy
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonMacroscopicRichSignedAmplitude WilsonMSDictionaryVector WilsonCenteredFourOutputSensor GapsContact.Seams
open OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree WilsonCenteredFourOutputBranch
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedRawPair WilsonCenteredNestedProgram
open private twoRows from YM.Integration.WilsonCenteredFourOutputTreePrice
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
    {arch:Arch R.family}(bliss:Bliss F l arch Y)(V:Store G)(salary:WilsonThermometerWeakPairSector.Salary F Q J)(c:Q.channels 4)
    {cap:ℕ}(included:4≤cap)(other:S.Tag)(m:ℕ)(out:Q.channels m){radius η:ℝ}(Rn:0≤radius)(ηp:0<η):
    Nesting.Uniform F Q ∧ LogTrace F Q.port ∧
    ∃B:Profiles R 4,∃w:B.probes.index→Atom (R:=R) 4,
    ∃issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid 4 (w j),
    ∃(k j l₀:ℕ)(H L:ℝ),0≤H ∧ 0≤L ∧ ∀(g:ℝ→ℝ),Coupling G g→
    ∀(K:Set (Points 2)),IsCompact K→K⊆conf 2→∃(E:ℕ)(C:ℝ),0≤C ∧ ∀P A b:ℕ,P+E≤A→
    ∀(v:Fin 2→Free R.family 4)(ψ:Test 2),tsupport ψ⊆K→∀q:ℕ,∃W:ℝ,0≤W ∧
    ∀ᶠr in trail, let t:=r/((g r)^A)^2
    ∃ tp:0<t,∀D:ℝ,
      let pub:=homogeneous F J Z r
      let u:=fun i=>pub 4 (v i)
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      let observed:=fun j=>appeared F (d:=d₄) u (X j) r ψ
      let bank:=((ms.separatedOPE ν).wilson.light 4).choose
      let value:=fun s=>experiment R.family d₄ 4 Z M ν v ψ bank q (g r) s
      let forecast:=prediction R.family d₄ 4 Z M ν v ψ q (g r)
      let fee:=(∫x:Points 2,‖ψ x‖)*(∏i,‖v i‖)*C+D
      (∃ᶠs:ℝ in atTop,‖observed-(fun j=>(X j).charge F 4 (pub 4 (value s)))‖≤D*g r^(P+A*9))→
      ∀(y:Fin 2→E4)(o:E4),y 0=0→
      let θ:=WilsonThermometerWeakPairClock.scale g b r
      (∀i,‖y i-o‖≤radius*θ)→(∀i j,i≠j→η*θ≤‖y i-y j‖)→∀A':Rule F Q,
      let pupils:=placed F Q (tip F Q included c) other
      let N:=A' 2 m out θ (g θ) y pupils o
      let error:=express Q m out y pupils o-N
      ∀(n p:ℕ)(δ:ℝ),let ticket':=δ*(g θ)^p*shell θ^n*(θ^m/(θ^4*θ^other.1))
      |error.re|≤ticket'→|error.im|≤ticket'→
      ‖heard F Q included c m out u other r ψ y o - grade F Q c (pub 4 forecast)*N‖≤
        (H*dock r^k*r^4*fee*(g r)^P)*(L*shell θ^j*(θ^m/(θ^4*θ^other.1)))+
        (W*dock r^l₀*r^4)*(2*ticket'):=by
  obtain ⟨logarithmic,B,w,issued,k,H,h0,read⟩:=WilsonCenteredFourOutputSmooth.original F J Z M ν ms lead owed Q fac lo bill bliss V salary c
  obtain ⟨j,L,l0,salary'⟩:=WilsonCenteredNestedLoggedRow.original F Q fac.toServices logarithmic.toSingleLog
    (placed F Q (tip F Q included c) other) m out Rn ηp
  obtain ⟨l₀,forecast⟩:=WilsonCenteredFourPublicForecast.original F Q J Z M ν simple bliss bill V lead owed c
  refine ⟨Nesting.uniform F Q fac.toServices,logarithmic,B,w,issued,k,j,l₀,H,L,h0,l0,?_⟩
  intro g hg K compact apart
  obtain ⟨E,C,c0,inner⟩:=read g hg K compact apart
  refine ⟨E,C,c0,?_⟩;intro P A b budget v ψ cover q
  obtain ⟨W,w0,posted⟩:=forecast g hg v ψ q
  refine ⟨W,w0,?_⟩
  have compass:=(WilsonThermometerWeakPairClock.small simple g hg b).eventually salary'
  filter_upwards [inner P A budget,compass,posted] with r near coarse issuedForecast
  obtain ⟨tp,pay⟩:=near
  refine ⟨tp,?_⟩
  intro D pub u X observed bank value pred fee experiment y o center θ ball distance A' pupils N error n p δ ticket' re im
  rw [WilsonCenteredFourOutputBranch.deposited F Q included c m out u other r ψ y o center]
  have outer:=coarse y o ball distance
  rw [Fin.prod_univ_two] at outer
  have bound:=twoRows (pay v ψ cover q D experiment) outer
    (Y':=N)
  have signed:‖error‖≤2*ticket':=(Complex.norm_le_abs_re_add_abs_im error).trans (by linarith only [re,im])
  exact bound.trans (add_le_add le_rfl (mul_le_mul issuedForecast signed (norm_nonneg _) ((norm_nonneg _).trans issuedForecast)))

end YM.Integration.WilsonCenteredFourOutputSmoothTree
