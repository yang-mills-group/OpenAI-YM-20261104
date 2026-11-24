import YM.Integration.WilsonPublicForkTightVertex

/-! The complete ordinary field and each retained column are observed with the
same physical exterior. Its fitted coordinates never enter the inverse. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMovingForkSameExterior
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
open WilsonPublicForkPublicRows (probe)
open WilsonMacroscopicRichPositionRows (profile)

theorem original {simple:G.Simple}{κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (V:XSpace.Normalize.Store G){course:Almanac F}{Y:(Bel R.family.book).Hierarchy}
    {U:Ultrafilter (ℕ×ℕ)}{arc:Arch R.family}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F course Q J Y arc U simple cohort)(h:ℕ):
    LogTrace F Q.port ∧ ∃B:Profiles R h,∃w:B.probes.index→Atom (R:=R) h,
    ∃issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
    ∀g:ℝ→ℝ,Coupling G g → ∀(n:ℕ)(d:Fin n→ℕ)(box:Set (Points n)),IsCompact box → box⊆conf n →
    ∃(E:ℕ)(C:ℝ),0≤C ∧ ∀ε:ℝ,0<ε → ∃ K:ℝ,0≤K ∧ ∀m:ℕ,0 < m → ∀ᶠr in trail,
    let ρ:=((g r)^m)^2
    let t:=r/ρ
    ∃tp:0<t,∀(v:∀i,RG17.Free R.family (d i))(ψ:Test n),tsupport ψ⊆box → ∀q:ℕ,
    let pub:=homogeneous F J Z r
    let actual:=RG17.basket Q h (d:=d) (fun i=>pub (d i) (v i)) r ψ
    let target:=prediction R.family d h Z M ν v ψ q (g r)
    let basis:=WilsonMSDictionaryVector.basis R.family h
    let c:=fun k=>basis.repr target k
    let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
    let obs:=fun j=>RG17.appeared F (d:=d) (fun i=>pub (d i) (v i)) (X j) r ψ
    let paired:=fun k j=>(X j).charge F h (pub h (basis k))
    let residual:=obs-∑k,c k • paired k
    let spatial:=((∫x:Points n,‖ψ x‖)*(∏i,‖v i‖)*C)*ρ^(h+1)/(g r)^E
    ‖(pub h).symm actual-target‖≤K*ρ^(-(h:ℝ)-ε)*(spatial+‖residual‖):=by
  obtain ⟨B,w,issued,windows⟩:=WilsonPublicForkTightPivot.original F J Z run.leading run.obeys simple h
  refine ⟨OPE.tickets_suffice F run.facilities run.original run.matrix Q.spans,B,w,issued,?_⟩
  intro g hg n d box compact clear
  obtain ⟨E,C,cp,cost⟩:=WilsonPublicForkPanel.original F fund course run.phases run.facilities run.bliss run.matrix
    Q run.foundation J V run.leading Z run.obeys d h B w issued g hg box compact clear
  refine ⟨E,C,cp,fun ε ep=>?_⟩
  obtain ⟨K,kp,purchased⟩:=windows ε ep
  refine ⟨K,kp,fun m mp=>?_⟩
  filter_upwards [purchased g hg m,cost m mp,hg.positive] with r fit fare gp
  intro ρ t
  obtain ⟨tp,read⟩:=fit
  refine ⟨tp,?_⟩
  intro v ψ spread q pub actual target basis c X obs paired residual spatial
  let dst:=(pub h) target
  let U:=WilsonMatrixTicketLanesSmearedPivot.row F J Z B t
  have hear(y:S.Field h):(fun j=>(X j).charge F h y)=U y:=
    funext fun j=>WilsonPublicOutputSmooth.charge F J Z B w issued tp y j
  have eq:U dst=∑k,c k • paired k:=by
    have hold:dst=∑k,c k • (pub h) (basis k):=by
      calc
        dst=(pub h) (∑k,c k • (basis k)):=congrArg (pub h) (basis.sum_repr target).symm
        _=_:=by simp only [map_sum,map_smul]
    rw [hold,map_sum]
    apply Finset.sum_congr rfl;intro k _
    rw [map_smul,←hear]
  have seen:‖U actual-obs‖ ≤ spatial:=by
    rw [←hear actual]
    exact fare tp v ψ spread
  have bound:=read (actual-dst)
  rw [hear,U.map_sub] at bound
  have pp:0≤K*ρ^(-(h:ℝ)-ε):=mul_nonneg kp (Real.rpow_nonneg (sq_nonneg _) _)
  have report:‖obs-U dst‖=‖residual‖:=by rw [eq]
  have pay:=bound.trans (mul_le_mul_of_nonneg_left
    ((norm_sub_le_norm_sub_add_norm_sub _ obs _).trans (add_le_add seen report.le)) pp)
  simpa only [dst,pub,map_sub,LinearEquiv.symm_apply_apply] using pay

end YM.Integration.WilsonMovingForkSameExterior
