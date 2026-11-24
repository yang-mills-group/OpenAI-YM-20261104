import YM.Integration.WilsonPublicForkRelease
import YM.Integration.WilsonPublicForkReadings
import YM.Integration.WilsonPublicForkTestFee

/-! The original moving finite detector bounded uniformly on the full smooth L¹
profile ball. Each normalization is applied at its genuine ordered regulator. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkSmoothBall
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
    IsCompact box → box⊆conf n → ∃ (E:ℕ)(fee:ℝ),0≤fee ∧ ∀ q:ℕ, ∃ gramFee:ℝ,0≤gramFee ∧ ∀ P A:ℕ,0<A → P+E≤A →
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
    ∀ (ψ:Test n) (a₁ a₂ a₃:ℝ),tsupport ψ⊆box → 0≤a₁ → 0≤a₂ → 0≤a₃ →
      let amplitude:=(∏i,‖v i‖)*(∫x:Points n,‖ψ x‖)
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      let near:=fun i=>pub (d i) (v i)
      let physical:=RG17.basket Q h (d:=d) near r ψ
      let bank:=((ms.separatedOPE ν).wilson.light h).choose
      let issuedMS:=fun s=>experiment R.family d h Z M ν v ψ bank q (g r) s
      let D:=fee+a₁+a₃+gramFee*a₂
      let η:=(g r)^(P+A*(2*h+1))
      ∀ (ordinary:ℝ → UVIndex → B.probes.index → ℂ)
        (gram:ℝ → UVIndex → Dframe.Toon G h → B.probes.index → ℂ),
      (∃ᶠ s:ℝ in atTop, f.late fun N per=>
        (∀j,‖packMark L (X j) d ins r ψ (N,per)-ordinary s (N,per) j‖≤(a₁*amplitude)*η) ∧
        (∀k j,‖headMark L (X j) h r (N,per) (out k)-gram s (N,per) k j‖≤a₂*η) ∧
        ∀j,‖ordinary s (N,per) j-∑k,axis.repr (issuedMS s) k*gram s (N,per) k j‖≤(a₃*amplitude)*η) →
      ‖(pub h).symm physical-prediction R.family d h Z M ν v ψ q (g r)‖ ≤ K*D*amplitude*(g r)^P := by
  obtain ⟨logged,B,w,issued,K,kp,read⟩:=WilsonPublicForkRelease.original F J Z M ν ms fund course done' V
    lead owed Q book fac bliss ticket L growing fees h
  refine ⟨logged,B,w,issued,K,kp,?_⟩
  intro g hg n d box compact spread
  obtain ⟨E,fee,fp,budget⟩:=read g hg n d box compact spread
  refine ⟨E,fee,fp,?_⟩
  intro q
  obtain ⟨gramFee,fpos,investment⟩:=WilsonPublicForkTestFee.inversion R.family d h Z M ν ms box compact spread q
  refine ⟨gramFee,fpos,?_⟩
  intro P A ap clock v
  obtain ⟨a,c,returned⟩:=budget P A ap clock v
  refine ⟨a,c,?_⟩
  filter_upwards [returned,hg.positive,(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with r hire gp one
  dsimp only at hire ⊢
  obtain ⟨tp,ins,out,invoices,heads,hear⟩:=hire
  refine ⟨tp,ins,out,invoices,heads,?_⟩
  intro ψ a₁ a₂ a₃ inside pa pb pc ordinary gram signed
  let amplitude:=(∏i,‖v i‖)*(∫x:Points n,‖ψ x‖)
  have nonneg:0≤amplitude:=mul_nonneg (Finset.prod_nonneg fun _ _=>norm_nonneg _) (integral_nonneg fun _=>norm_nonneg _)
  let C:=(∫x:Points n,‖ψ x‖)*(∏i,‖v i‖)*fee
  let rhs:=fun δ:ℝ=>K*(C+(a₁*amplitude+a₃*amplitude+(gramFee*amplitude+δ)*a₂))*(g r)^P
  have limit:Continuous rhs:=by dsimp only [rhs];fun_prop
  have upto(δ:ℝ)(dp:0<δ):
      ‖((homogeneous F J Z r) h).symm (RG17.basket Q h (d:=d) (fun i=>homogeneous F J Z r (d i) (v i)) r ψ)-
        prediction R.family d h Z M ν v ψ q (g r)‖≤rhs δ:=by
    have cash:=investment v ψ inside (g r) ⟨by linarith,one⟩ δ dp
    have signed' := WilsonPublicForkReadings.ordered F L _ d h ψ ins out r _
      (add_nonneg (mul_nonneg fpos nonneg) dp.le) (by simpa only [amplitude,mul_assoc] using cash) (a₁*amplitude) a₂ (a₃*amplitude) _
      (mul_nonneg pa nonneg) pb (mul_nonneg pc nonneg) (pow_nonneg gp.le _) ordinary gram signed
    exact (hear ψ q _ inside signed').2
  have lim:Tendsto rhs (𝓝[>] 0) (𝓝 (rhs 0)):=(limit.tendsto 0).mono_left nhdsWithin_le_nhds
  have paid:=ge_of_tendsto lim ((show ∀ᶠ δ:ℝ in 𝓝[>] 0,0<δ from self_mem_nhdsWithin).mono (fun δ dp=>upto δ dp))
  exact paid.trans_eq (by dsimp only [rhs,C,amplitude];ring)

end YM.Integration.WilsonPublicForkSmoothBall
