import YM.Integration.WilsonMovingForkProfileGrid
import YM.Integration.WilsonMovingForkOwnRadiusSites
import YM.Integration.WilsonMovingForkElectedCaptureStops

/-! The numerator and every Gram column on one growing physical box and one booked exterior. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 840000
noncomputable section
namespace YM.Integration.WilsonMovingForkOwnRadiusPanel
open Function Filter Set MeasureTheory Metric Lattice Wilson RG Source Extraction Table Spec RG17 Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedBranchStencil WilsonSeparatedGridTree
open Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open FVA2.O MS MS.Land MS.Theater
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichPositionRows WilsonMacroscopicRichMovingPlane
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry
open WilsonMovingForkPositionIntegrals WilsonMovingForkProbeMaster WilsonMovingForkProbeDates
open WilsonMovingForkSampleBank WilsonMovingForkLocatedSamples
open Pert.Asymptotics
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonPublicForkPublicRows (probe)
open scoped Classical Topology BigOperators
attribute [local instance] Trial.count
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
    (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){n h:ℕ}(d:Fin n→ℕ)(v:∀i,Free R.family (d i))
    (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
local notation "a" => R.family.S.a
local notation "Kind" => Option (Dframe.Toon G h)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (T A reserve depth:ℕ){δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z (cap h d) T s.val)
    (j:B.probes.index)(K:Set (Points n))(compact:IsCompact K)(separated:K⊆conf n):
    let φ:=profile (B.probes.shell j) (w j) (issued j) (test B j)
    let source:=dose d v (probe B w)
    ∃M:ℝ,0<M ∧ ∃η:ℝ,0<η ∧ ∃σ:ℝ,0<σ ∧ ∃width:ℕ,∀(E:Type)[Fintype E](P:ℕ),
      ∃order:Kind→ℕ,∃price:Kind→ℝ,(∀k,0≤price k) ∧ ∀ᶠr in trail,∀rp:0<r,∀inBook:r<δ,
      ∀t:{s:ℝ // 0<s ∧ s<δ},r≤t.val → t.val=outer z A r → r/t.val≤σ →
      let ρ:=dates (P:=B.probes.index) (G:=G) (h:=h) (n:=n) ⟨r,rp,inBook⟩ t
      let f₀:=reporter F books ρ
      let cutoff:=WilsonInvariantActionPosition.berth R reserve f₀
      let captured:=WilsonMovingForkOwnRadiusSites.capture R.family.S (M+1) r t.val
      captured≤f₀ ∧ a captured/a f₀≤R.family.path.levels.clock.hatBeta f₀^((2*T+11+2*A)+2*A+2) ∧
      (∀u N per,u≤captured → captured≤N →
        R.family.S.scale captured-R.family.S.scale u ≤
          4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per captured)⁻¹ →
        a u/a cutoff≤R.family.path.levels.clock.hatBeta u^width ∧
          R.family.S.scale cutoff-R.family.S.scale u≤(width:ℝ)*(1+Real.log (R.family.path.levels.clock.hatBeta (u+1)))) ∧
      let dp:=div_pos (R.family.S.a_pos f₀) rp
      let arm:=fun s=>homogeneous F J Z (ρ s).val (bound d s).val (source s)
      let obs(k:Kind)(x:Points (arity n k)):=S.classMoment S (fun i=>(bound d (ports j k i)).val) x
        (fun i=>arm (ports j k i))
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued t.property.1 j
      let pub:=homogeneous F J Z r
      ∀ψ:Test n,tsupport ψ⊆K → ∀ε:ℝ,0<ε → ∀ref:E→E4,
      let Y:=RG17.appeared F (d:=d) (fun i=>pub (d i) (v i)) X r ψ
      let mat:=fun k=>X.charge F h (pub h (WilsonMSDictionaryVector.basis R.family h k))
      ∃ι:Type,∃_:Fintype ι,∃x:ι→space ψ φ,∃μ:ι→ℂ,∃κ:Type,∃_:Fintype κ,∃zz:κ→tsupport φ,∃ν:κ→ℂ,
      (∑i,‖μ i‖)≤Read.Value ψ*Read.Value φ+ε ∧ (∑b,‖ν b‖)≤Read.Value φ+ε ∧
      let pos:=fun u:Index ι κ G h=>site (fun i=>nearSite r t.val (x i).val) (fun b=>farSite r t.val (zz b).val) u
      let chart u:=sold (order (kind u)) ref dp (pos u)
      ∃o:∀u,(chart u).sample→Fin (arity n (kind u))→ Cover,
      (∀u b,tag (a f₀) (o u b)=r • (chart u).site b ∧ tag (a f₀) (o u b)∈generic _ ∧
        (∀i,‖R.family.S.gridPoint f₀ (o u b i)‖≤(M+1)*t.val) ∧
        WilsonMovingForkOwnRadiusSites.Recorded R f₀ captured (o u b) ∧
        Pairwise fun i k=>(η/2)*r≤‖R.family.S.gridPoint f₀ (o u b i)-R.family.S.gridPoint f₀ (o u b k)‖) ∧
      ∀c:Dframe.Toon G h→ℂ,let coin u (b:(chart u).sample):=mix μ ν c u*((chart u).weight b:ℂ)
        (∑u,∑b:(chart u).sample,‖coin u b‖)≤∑u,‖mix μ ν c u‖*(total (arity n (kind u)) (order (kind u)) E)^levels (arity n (kind u)) ∧
        ‖(Y-∑k,c k*mat k)-∑u,∑b:(chart u).sample,coin u b*obs (kind u) (tag (a f₀) (o u b))‖≤
          (ε+∑k,‖c k‖*ε)+∑u,‖mix μ ν c u‖*(price (kind u)*(∏i,‖source (ports j (kind u) i)‖)*(wilson z r)^P) :=by
  intro φ source
  obtain ⟨M,mp,η,ep,σ,sp,programme⟩:=
    WilsonMovingForkProfileGrid.original F J Z d v B w issued simple bliss slow lead owed T A books j K compact separated
  have lp:0≤M+1:=by linarith
  obtain ⟨width,stop⟩:=WilsonMovingForkElectedCaptureStops.original (I:=Seat G n h B.probes.index) F simple bliss slow (cap h d) T A reserve depth
    (bound d) books lp
  refine ⟨M,mp,η,ep,σ,sp,width,?_⟩
  intro E _ P
  obtain ⟨ord,C,cn,draw⟩:=programme E P
  refine ⟨ord,C,cn,?_⟩
  have raw:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have pos:0<a 0/(16*(1+(M+1))):=div_pos (R.family.S.a_pos _) (by positivity)
  have nearby:=(WilsonThermometerUnitFilingFourPoolClock.longer F simple bliss A).eventually (Ioc_mem_nhdsGT pos)
  filter_upwards [draw,stop,nearby,raw.positive,(raw.conforms simple).eventually
    (ge_mem_nhds zero_lt_one),WilsonOriginalTwoFlatPublicMixedMesh.original (I:=Seat G n h B.probes.index) F simple bliss slow (cap h d) T A (bound d) books]
    with r receipt terms small gp gu mesh
  intro rp paid t rt atHome gap ρ f₀ cutoff captured
  let base:{s:ℝ//0<s ∧ s<δ}:=⟨r,rp,paid⟩
  have named:=@WilsonMovingForkProbeDates.file_dates G n h B.probes.index δ base t
  have homes:∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z A r:=fun i=>
    ⟨(named.2.2 rt i).1,((named.2.2 rt i).2).trans atHome.le⟩
  obtain ⟨arrived,lengths,back⟩:=terms ρ homes named.2.1 t.val rt atHome.le
  refine ⟨arrived,lengths,back,?_⟩
  have af:a f₀≤r:=by
    have hq:=(div_le_iff₀ rp).mp (mesh ρ homes named.2.1).1
    exact hq.trans ((mul_le_mul_of_nonneg_right (pow_le_one₀ gp.le gu) rp.le).trans_eq (one_mul _))
  have bounded:WilsonMovingForkOwnRadiusSites.size (M+1) r t.val≤a 0:=by
    rw [WilsonMovingForkOwnRadiusSites.expanded _ rp]
    have cap₀:=(le_div_iff₀ (show 0<16*(1+(M+1)) by positivity)).mp small.2
    rw [←atHome] at cap₀
    linarith only [cap₀,rt]
  intro dp arm obs X pub ψ support ε positive ref Y mat
  obtain ⟨ι,_,x,μ,κ,_,z₂,ν,payX,payZ,rest⟩:=receipt rp paid t rt atHome.le gap ψ support ε positive ref
  refine ⟨ι,inferInstance,x,μ,κ,inferInstance,z₂,ν,payX,payZ,?_⟩
  intro pos chart
  obtain ⟨o,positions,refund⟩:=rest
  refine ⟨o,?_,refund⟩
  intro u b
  obtain ⟨point,joint,wall,clear⟩:=positions u b
  rw [←atHome] at wall
  exact ⟨point,joint,wall,WilsonMovingForkOwnRadiusSites.recorded R lp rp t.property.1.le bounded af _ wall,clear⟩

end YM.Integration.WilsonMovingForkOwnRadiusPanel
end
