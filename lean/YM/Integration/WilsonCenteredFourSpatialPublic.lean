import YM.Integration.WilsonCenteredFourSpatialMixedCharge
import YM.Integration.WilsonCenteredFourSpatialPanel

/-! The real moving homogeneous colors on all three inputs, tested on the
independently displaced finite two-site panel of the original frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialPublic
open Function Filter Set Finset MeasureTheory Table Spec RG17 OPE OPE.Orbits
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato XSpace.Normalize
open WilsonMacroscopicRichSignedAmplitude WilsonThermometerWeakPairClock WilsonMacroscopicRichTwoDatePivot
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale Pert Pert.Position MS MS.Local.Physical XSpace
open MS.Menus MS.Land MS.Theater RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
local notation "d₄" => (fun _:Fin 2=>4)

theorem original {Y:(Bel R.family.book).Hierarchy}(V:Store G)(simple:G.Simple)
    (lead:Leading F J)(owed:∀d,∀ᶠt in trail,Frame.obedient F Y (J t) d)
    (salary:WilsonThermometerWeakPairSector.Salary F Q J)(fac:Services R.family f S)
    (B:Profiles R 4)(w:B.probes.index→Atom (R:=R) 4)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid 4 (w j))
    (g:ℝ→ℝ)(hg:Coupling G g)(K:Set (Points 2))(compact:IsCompact K)(spread:K⊆conf 2):
    ∃(E:ℕ)(C:ℝ),0≤C ∧ ∀ A:ℕ,E≤A→∀ᶠ r in trail,
      let t:=r/((g r)^A)^2
      ∀(tp:0<t)(v:Fin 2→RG17.Free R.family 4)(ψ:Test 2),tsupport ψ⊆K→
      let u:=fun i=>homogeneous F J Z r 4 (v i)
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
      ‖(fun j=>(X j).charge F 4 (basket Q 4 (d:=d₄) u r ψ)) -
        (fun j=>appeared F (d:=d₄) u (X j) r ψ)‖ ≤
        ((∫x:Points 2,‖ψ x‖)*(∏i,‖v i‖)*C)*(((g r)^A)^2)^5/(g r)^E:=by
  let φ:=fun j=>profile (B.probes.shell j) (w j) (issued j) (test B j)
  let b:=fun j=>(Bel R.family.book).project 4 (w j)
  choose D C c0 pay using fun j=>WilsonCenteredFourSpatialMixedCharge.original F Q J V simple g hg lead salary fac K compact spread (φ j)
  obtain ⟨L,l0,payL⟩:=WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple 4
  let E:=1+∑j,D j
  let W:=fun j=>(∫z:Points 2,‖φ j z‖)*C j*L^2*(L*‖b j‖)
  have W0(j):0≤W j:=by dsimp only [W];have:=c0 j;positivity
  refine ⟨E,∑j,W j,Finset.sum_nonneg (fun j _=>W0 j),?_⟩
  intro A ea
  have ready(j:B.probes.index):D j+(A*2-E)+1≤A*2:=by
    have h:=Finset.single_le_sum (f:=D) (fun k (_:k∈Finset.univ)=>Nat.zero_le _) (Finset.mem_univ j)
    dsimp only [E] at *;omega
  have all:=eventually_all.mpr (fun j=>pay j (A*2-E) 1 zero_lt_one (A*2) (ready j))
  filter_upwards [all,payL,(small simple g hg (A*2)).eventually payL,hg.positive,self_mem_nhdsWithin]
    with r paid near far gp (rp:0<r)
  dsimp only;intro tp v ψ inside
  let t:=r/((g r)^A)^2
  have clock:scale g (A*2) r=t:=by rw [scale,pow_mul]
  rw [clock] at far
  let y:=fun i=>active F J Z r 4 (v i)
  let u:=fun i=>homogeneous F J Z r 4 (v i)
  have placed:(fun i=>J r 4 (y i))=u:=by funext i;simp [y,u,active,LinearEquiv.trans_apply]
  have fees:(∏i,‖y i‖)≤L^2*(∏i,‖v i‖):=by
    calc _ ≤ ∏i,L*‖v i‖:=Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>near (v i))
         _ = _:=by rw [Finset.prod_mul_distrib];simp
  let mass:=∫x:Points 2,‖ψ x‖
  have m0:0 ≤ mass:=integral_nonneg fun _=>norm_nonneg _
  have vs:0≤∏i,‖v i‖:=Finset.prod_nonneg fun _ _=>norm_nonneg _
  have total:0≤∑j,W j:=Finset.sum_nonneg (fun j _=>W0 j)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have h:=paid j;rw [clock] at h
  have actual:=(h tp y (active F J Z t 4 (b j))).2 ψ inside
  change ‖appeared F (d:=d₄) (fun i=>J r 4 (y i)) _ r ψ - External.charge F _ 4 (basket Q 4 (d:=d₄) (fun i=>J r 4 (y i)) r ψ)‖ ≤ _ at actual
  rw [placed] at actual
  change ‖External.charge F _ 4 (basket Q 4 (d:=d₄) u r ψ) - appeared F (d:=d₄) u _ r ψ‖≤_
  rw [norm_sub_rev]
  have phase:0≤g r^(A*2-E)*(r/t)^4:=by positivity
  have mj:0≤∫z:Points 2,‖φ j z‖:=integral_nonneg fun _=>norm_nonneg _
  calc
    _ ≤ mass*((∫z:Points 2,‖φ j z‖)*(C j*(∏i,‖y i‖)*(‖active F J Z t 4 (b j)‖*(1*g r^(A*2-E)*(r/t)^4)))):=actual
    _ ≤ mass*((∫z:Points 2,‖φ j z‖)*(C j*(L^2*∏i,‖v i‖)*((L*‖b j‖)*(1*g r^(A*2-E)*(r/t)^4)))):=by
      have cpos:=c0 j;gcongr;first | exact cpos | exact fees | exact far (b j)
    _ = (mass*(∏i,‖v i‖)*W j)*(g r^(A*2-E)*(r/t)^4):=by dsimp only [W];ring
    _ ≤ (mass*(∏i,‖v i‖)*(∑i,W i))*(g r^(A*2-E)*(r/t)^4):=by
      gcongr;exact Finset.single_le_sum (fun i (_:i∈Finset.univ)=>W0 i) (Finset.mem_univ j)
    _ = _:=by rw [WilsonCenteredFourSpatialPanel.engineering gp rp A E ea];ring

end YM.Integration.WilsonCenteredFourSpatialPublic
