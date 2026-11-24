import YM.Integration.WilsonCenteredFourSpatialCharge
import YM.Integration.WilsonPublicOutputSmooth

/-! Every original far profile is chosen before the measuring window opens.
The full finite pivot row has the true fifth engineering power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialPanel
open Function Filter Set Finset MeasureTheory Table Spec RG17 OPE OPE.Orbits
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato XSpace.Normalize
open WilsonMacroscopicRichSignedAmplitude WilsonThermometerWeakPairClock WilsonMacroscopicRichTwoDatePivot
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale Pert Pert.Position MS MS.Local.Physical XSpace
open MS.Menus MS.Land MS.Theater RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)

theorem engineering {g r:ℝ}(gp:0<g)(rp:0<r)(A E:ℕ)(ea:E≤A):
    g^(A*2-E)*(r/(r/(g^A)^2))^4= ((g^A)^2)^5/g^E:=by
  have left:r/(r/(g^A)^2)=(g^A)^2:=by field_simp [gp.ne',rp.ne']
  rw [left];apply (eq_div_iff (pow_ne_zero _ gp.ne')).mpr
  calc g^(A*2-E)*((g^A)^2)^4*g^E=(g^(A*2-E)*g^E)*((g^A)^2)^4:=by ring
       _=_:=by rw [←pow_add,Nat.sub_add_cancel (by omega:E≤A*2),pow_mul];ring

theorem original {Y:(Bel R.family.book).Hierarchy}(V:Store G)(simple:G.Simple)
    (lead:Leading F J)(owed:∀d,∀ᶠt in trail,Frame.obedient F Y (J t) d)
    (salary:WilsonThermometerWeakPairSector.Salary F Q J)
    (B:Profiles R 4)(w:B.probes.index→Atom (R:=R) 4)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid 4 (w j))
    (g:ℝ→ℝ)(hg:Coupling G g)(v:Fin 2→RG17.Free R.family 4)
    (K:Set (Points 2))(compact:IsCompact K)(spread:K⊆conf 2):
    ∃(E:ℕ)(C:ℝ),0≤C ∧ ∀ A:ℕ,E≤A→∀ᶠ r in trail,
      let t:=r/((g r)^A)^2
      ∀(tp:0<t)(x:Points 2),x∈K→
      ‖row F J Z B t (WilsonPublicOutputRows.packet F J Q 4 (fun _:Fin 2=>4) v r x) -
        sample F J Z B w issued tp r x (fun i=>⟨4,v i⟩)‖ ≤ C*(((g r)^A)^2)^5/(g r)^E:=by
  let φ:=fun j=>profile (B.probes.shell j) (w j) (issued j) (test B j)
  let b:=fun j=>(Bel R.family.book).project 4 (w j)
  choose D C c0 pay using fun j=>WilsonCenteredFourSpatialProfile.original F Q J V simple g hg lead salary v K compact spread (φ j)
  obtain ⟨L,l0,bounded⟩:=WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple 4
  let E:=1+∑j,D j
  let wage:=fun j=>(∫z:Points 2,‖φ j z‖)*(C j*(L*‖b j‖))
  have w0(j):0≤wage j:=by dsimp only [wage];exact mul_nonneg (integral_nonneg fun _=>norm_nonneg _) (mul_nonneg (c0 j) (mul_nonneg l0 (norm_nonneg _)))
  refine ⟨E,∑j,wage j,Finset.sum_nonneg (fun j _=>w0 j),?_⟩
  intro A ea
  have ready(j:B.probes.index):D j+(A*2-E)+1≤A*2:=by
    have h:=Finset.single_le_sum (f:=D) (fun k (_:k∈Finset.univ)=>Nat.zero_le _) (Finset.mem_univ j)
    dsimp only [E] at *;omega
  have all:=eventually_all.mpr (fun j=>pay j (A*2-E) 1 zero_lt_one (A*2) (ready j))
  filter_upwards [all,(small simple g hg (A*2)).eventually bounded,hg.positive,self_mem_nhdsWithin]
    with r paid bounded gp (rp:0<r)
  dsimp only;intro tp x hx
  let t:=r/((g r)^A)^2
  have clock:scale g (A*2) r=t:=by rw [scale,pow_mul]
  have exp0:0≤((g r)^A)^2:=by positivity
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg (Finset.sum_nonneg fun j _=>w0 j) (pow_nonneg exp0 _)) (pow_nonneg gp.le _))).mpr
  intro j
  have cash:=paid j;rw [clock] at cash bounded
  have due:=cash tp x hx (active F J Z t 4 (b j))
  let measured:=WilsonPublicOutputRows.packet F J Q 4 (fun _:Fin 2=>4) v r x
  change ‖reading J (φ j) tp ⟨4,active F J Z t 4 (b j)⟩ r x (fun i=>⟨4,v i⟩) -
    (stencil J (φ j) tp ⟨4,active F J Z t 4 (b j)⟩).charge F 4 measured‖≤_ at due
  rw [show (stencil J (φ j) tp ⟨4,active F J Z t 4 (b j)⟩).charge F 4 measured = row F J Z B t measured j from
    WilsonPublicOutputSmooth.charge F J Z B w issued tp measured j] at due
  change ‖row F J Z B t measured j-sample F J Z B w issued tp r x (fun i=>⟨4,v i⟩) j‖≤_
  rw [norm_sub_rev]
  have mass:0≤∫z:Points 2,‖φ j z‖:=integral_nonneg fun _=>norm_nonneg _
  calc
    _ ≤ (∫z:Points 2,‖φ j z‖)*(C j*‖active F J Z t 4 (b j)‖*(1*g r^(A*2-E)*(r/t)^4)):=due
    _ ≤ wage j * (g r^(A*2-E)*(r/t)^4):=by
      dsimp only [wage];rw [one_mul,←mul_assoc];gcongr <;> first | exact c0 j | exact bounded (b j)
    _ ≤ (∑i,wage i)*(g r^(A*2-E)*(r/t)^4):=mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i (_:i∈Finset.univ)=>w0 i) (Finset.mem_univ j)) (by positivity)
    _ = _:=by rw [engineering gp rp A E ea];ring

end YM.Integration.WilsonCenteredFourSpatialPanel
