import YM.Integration.WilsonPublicOutputRegulators

/-! The finite ordinary Wilson measurements returning one public OPE packet
through an arbitrary horizon. The physical cutoff and period precede the
independent far limit; all three readings use a single true field frame. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicOutputPhysical
open Function Filter Set MeasureTheory Extraction Table Spec OPE OPE.Orbits OPE.Log RG17
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open Maxwell XSpace XSpace.Normalize FVA2.O FVA2.O.Score MS MS.Land MS.Fleet MS.Theater
open Next.Rank RG12 SharpGram WilsonPositionHomogeneousFrame WilsonMSDictionaryVector
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonPublicOutputSmooth WilsonPublicOutputRegulators
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
    {simple:G.Simple} {σ:Prescription (Press.portDeck G)} {branch:Bool} (ms:Main.Match Z simple M σ branch)

/-- The original inputs and every output basis lift are named and priced before choosing the
inner profile, independent outer cutoff, and either regulator of the Wilson measurement. -/
theorem original {Y:(Bel R.family.book).Hierarchy} (lead:Leading F J)
    (owed:∀ d,∀ᶠ r in trail,Frame.obedient F Y (J r) d)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac:Facilities R.family f S) {l:Filter (ℕ×ℕ)} [l.NeBot] (selected:l≤f.fuse)
    (ticket:MatrixTicket (C:=R.family) S F.sector.derivatives l) (L:Layout F)
    (growing:Tendsto L.level trail atTop)
    (fees:∀ h, Pier.Lair.Paying F (Pier.Lair.tender F L J) h) (h:ℕ) :
    LogTrace F Q.port ∧
    ∃ B:Profiles R h, ∃ w:B.probes.index→Atom (R:=R) h,
    ∃ issued:∀ j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
    ∃ K:ℝ, 0≤K ∧ ∀ (g:ℝ→ℝ),Coupling G g → ∀ P E A:ℕ,P+E≤A →
    ∀ (n:ℕ) (d:Fin n→ℕ) (v:(i:Fin n)→RG17.Free R.family (d i)),
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
    ∀ (ψ:Test n) (q:ℕ) (C D:ℝ),0≤C →
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      let near:=fun i=>pub (d i) (v i)
      let physical:=RG17.basket Q h (d:=d) near r ψ
      let obs:=fun j=>RG17.appeared F near (X j) r ψ
      let bank:=((ms.separatedOPE ν).wilson.light h).choose
      let issuedMS:=fun s=>experiment R.family d h Z M ν v ψ bank q (g r) s
      (∀ j,packs (X j) r ψ) →
      (∀ j,Integrable (fun z:Points ((X j).n+1)=>(X j).test z*query F near ((X j).offset z) (X j).labels none r ψ)) →
      ‖(fun j=>(X j).charge F h physical)-obs‖ ≤ C*(((g r)^A)^2)^(h+1)/(g r)^E →
      (∃ᶠ s:ℝ in atTop, f.late fun N per=>
        ‖contrast F L X d ins out r ψ (issuedMS s) (N,per)‖ ≤ D*(g r)^(P+A*(2*h+1))) →
      (∃ᶠ s:ℝ in atTop, ‖(pub h).symm physical-issuedMS s‖ ≤ K*(C+D)*(g r)^P) ∧
      ‖(pub h).symm physical-prediction R.family d h Z M ν v ψ q (g r)‖ ≤ K*(C+D)*(g r)^P := by
  obtain ⟨logged,B,w,issued,K,kp,read⟩:=
    WilsonPublicOutputSmooth.original F J Z M ν ms lead owed Q fac selected ticket h
  refine ⟨logged,B,w,issued,K,kp,?_⟩
  intro g hg P E A clock n d v
  choose a lanes using (fun i=>columns F J Z L (d i) (fees (d i)))
  obtain ⟨c,outputs⟩:=columns F J Z L h (fees h)
  refine ⟨a,c,?_⟩
  have refs (i:Fin n):=growing.eventually_ge_atTop (R.family.ref (d i))
  filter_upwards [read g hg P E A clock,eventually_all.mpr lanes,outputs,
    eventually_all.mpr refs,growing.eventually_ge_atTop (R.family.ref h),length_rate.pos] with r consume inputs heads live href rp
  intro pub t β axis
  obtain ⟨tp,consume⟩:=consume
  choose ins iw identity using (fun i=>inputs i (v i))
  choose out ow named using (fun k=>heads (axis k))
  refine ⟨tp,ins,out,fun i=>⟨iw i,identity i⟩,fun k=>⟨ow k,named k⟩,?_⟩
  intro ψ q C D cp X near physical obs bank issuedMS cover int spatial signed
  apply consume n d v ψ q C D cp spatial
  exact WilsonPublicOutputRegulators.original F J Z L X d ins out r ψ near identity live named href rp
    cover int issuedMS (D*(g r)^(P+A*(2*h+1))) signed
end YM.Integration.WilsonPublicOutputPhysical
