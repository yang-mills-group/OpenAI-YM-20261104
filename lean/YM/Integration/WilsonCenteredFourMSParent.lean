import YM.Integration.WilsonCenteredFourPhysicalTree
import YM.Integration.WilsonOrdinaryNestedMSVertex

/-! The independent second vertex is the ordinary MS point program at the genuine
parent coupling and the true restored input coordinates. Its only local row is
the complete signed residual in the normalized public field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourMSParent
open Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits PhysMS Trace.Pilot Climb
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Theater Trace Trace.Terrace
open RG12 SharpGram OPE.Log PhysicalNext.Repeat.Legato OPE.Levy
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonMacroscopicRichSignedAmplitude WilsonMSDictionaryVector WilsonCenteredFourOutputSensor GapsContact.Seams
open OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree WilsonCenteredFourOutputBranch
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedRawPair WilsonCenteredNestedProgram
open EveryPhase WilsonLimitConstruction
universe u
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}
    (ms:Main.Match Z simple M σ branch)
local notation "d₄" => (fun _:Fin 2=>4)

def Hearing (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {cap:ℕ}(included:4≤cap)(other:S.Tag)(m:ℕ)(out:Q.channels m)(radius η:ℝ):Prop:=
    let c:=WilsonCenteredFourOutputRank.channel F Q J simple
    Fintype.card (Q.channels 4)=21 ∧ grade F Q c (Q.actor 4 c)=1 ∧
    (∀(d:ℕ)(p:d<4)(v:S.Field d),grade F Q c (F.sector.derivatives.rise p.le v)=0) ∧
    Nesting.Uniform F Q ∧ LogTrace F Q.port ∧
    ∃B:Profiles R 4,∃w:B.probes.index→Atom (R:=R) 4,
    ∃issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid 4 (w j),
    ∃(k j l₀:ℕ)(H L:ℝ),0≤H ∧ 0≤L ∧ ∀(g:ℝ→ℝ),Coupling G g→
    ∀(K:Set (Points 2)),IsCompact K→K⊆conf 2→∃(E:ℕ)(C:ℝ),0≤C ∧ ∀P A b:ℕ,P+E≤A→
    ∀(v:Fin 2→Free R.family 4)(ψ:Test 2),tsupport ψ⊆K→∀q:ℕ,∃W:ℝ,0≤W ∧
    ∀ᶠr in trail, let t:=r/((g r)^A)^2
    ∃ tp:0<t,∀(D:ℝ)(joint:ℝ→B.probes.index→ℂ)(gram:ℝ→Dframe.Toon G 4→B.probes.index→ℂ),
      let pub:=homogeneous F J Z r
      let u:=fun i=>pub 4 (v i)
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      let observed:=fun j=>appeared F (d:=d₄) u (X j) r ψ
      let bank:=((ms.separatedOPE ν).wilson.light 4).choose
      let value:=fun s=>experiment R.family d₄ 4 Z M ν v ψ bank q (g r) s
      let forecast:=prediction R.family d₄ 4 Z M ν v ψ q (g r)
      let fee:=(∫x:Points 2,‖ψ x‖)*(∏i,‖v i‖)*C+D
      (∃ᶠs:ℝ in atTop,WilsonCenteredFourFiniteSlate.invoice F X (pub 4) (value s) observed (joint s) (gram s)≤D*g r^(P+A*9))→
      ∀(y:Fin 2→E4)(o:E4),y 0=0→
      let θ:=WilsonThermometerWeakPairClock.scale g b r
      (∀i,‖y i-o‖≤radius*θ)→(∀i j,i≠j→η*θ≤‖y i-y j‖)→∀q':ℕ,
      let pupils:=placed F Q (tip F Q included c) other
      let N:=WilsonOrdinaryNestedMSVertex.program F Q J Z M ν q' 2 m out θ (g θ) y pupils o
      let signed:=WilsonOrdinaryNestedMSVertex.residual F Q J Z M ν m out q' θ (g θ) y o pupils
      ∀(n p:ℕ)(δ:ℝ),let ticket':=δ*(g θ)^p*shell θ^n
      ‖signed‖≤ticket'→
      ‖heard F Q included c m out u other r ψ y o - grade F Q c (pub 4 forecast)*N‖≤
        (H*dock r^k*r^4*fee*(g r)^P)*(L*shell θ^j*(θ^m/(θ^4*θ^other.1)))+
        (W*dock r^l₀*r^4)*(2*(ticket'*(θ^m/(θ^4*θ^other.1))))

theorem original {T:Campaign R}{W:Campaign.Pillars R T}{κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (L:Almanac F)(joined:Completed F L){Y:(Bel R.family.book).Hierarchy}(lead:Leading F J)
    (owed:∀d,∀ᶠr in trail, Frame.obedient F Y (J r) d)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac:Facilities R.family f S){l:Ultrafilter (ℕ×ℕ)}(lo:(l:Filter _)≤f.fuse)
    (bill:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    {arch:Arch R.family}(bliss:Bliss F l arch Y)(V:Store G)(book:Foundation F Q)
    {cap:ℕ}(included:4≤cap)(other:S.Tag)(m:ℕ)(out:Q.channels m){radius η:ℝ}(Rn:0≤radius)(ηp:0<η):
    Hearing F J Z M ν ms Q included other m out radius η:=by
  obtain ⟨card,self,lower,uniform,logged,B,w,issued,k,j,l₀,H',L',h0,l0,bought⟩:=
    WilsonCenteredFourPhysicalTree.original F J Z M ν ms fund L joined lead owed Q fac lo bill bliss V book included other m out Rn ηp
  refine ⟨card,self,lower,uniform,logged,B,w,issued,k,j,l₀,H',L',h0,l0,?_⟩
  intro g hg K compact apart
  obtain ⟨E,C,c0,inner⟩:=bought g hg K compact apart
  refine ⟨E,C,c0,?_⟩;intro P A b budget v ψ cover q
  obtain ⟨W₀,w0,released⟩:=inner P A b budget v ψ cover q
  refine ⟨W₀,w0,?_⟩
  filter_upwards [released,WilsonThermometerWeakPairClock.ordered simple g hg b,self_mem_nhdsWithin] with r sale rt rp
  obtain ⟨tp,sale⟩:=sale
  refine ⟨tp,?_⟩
  intro D joint gram pub u X observed bank value pred fee near y o center θ close apart' q' pupils N signed n p δ ticket' bound
  have pos:0<θ:=(show 0<r from rp).trans_le rt
  let rule:=WilsonOrdinaryNestedMSVertex.program F Q J Z M ν q'
  let error:=express Q m out y pupils o-N
  have restored:‖error‖=(θ^m/(θ^4*θ^other.1))*‖signed‖:=by
    have site:=WilsonOrdinaryNestedMSVertex.relative F Q J Z M ν m out q' θ (g θ) pos y o pupils
    rw [Fin.prod_univ_two] at site
    exact site
  have paid:‖error‖≤ticket'*(θ^m/(θ^4*θ^other.1)):=by
    rw [restored,mul_comm ticket']
    exact mul_le_mul_of_nonneg_left bound (by positivity)
  exact sale D joint gram near y o center close apart' rule n p δ
    ((Complex.abs_re_le_norm error).trans paid) ((Complex.abs_im_le_norm error).trans paid)

end YM.Integration.WilsonCenteredFourMSParent
