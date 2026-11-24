import YM.Integration.WilsonOrdinaryNestedReflectedSites
import YM.Integration.WilsonOrdinaryNestedWhole

/-! Return the actual fixed physical field to its normalized public position
coordinates on a comparable vertex with the sharp engineering power. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedInput
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom
open PhysMS Trace.Pilot GapsContact GapsContact.Seams GapsContact.Ascent
open Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater FVA2 FVA2.Register FVA2.Scale
open WilsonPositionHomogeneousFrame WilsonOrdinaryNestedMSVertex WilsonOrdinaryNestedLocal
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort) (Z:WilsonPrescription G)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z



open WilsonOrdinaryNestedReflectedSites OPE.Levy Push.FiniteDetection.Free

include run in
theorem reflected (d:ℕ) (v:S.Field d):
    ∃ (K:ℝ) (l:ℕ),0≤K ∧ ∀ᶠr:ℝ in trail,
      r^(2*d) * ‖OPE.Levy.pair d S (r • detectors) v (bar F d v)‖ ≤ K*dock r^l := by
  obtain ⟨M,η,Mp,ηp,room⟩:=WilsonOrdinaryNestedReflectedSites.geometry
  obtain ⟨K,l,Kp,priced⟩:=WilsonOrdinaryNestedWhole.original run (mark (F:=F) d v)
    (voids (S:=S)) Mp ηp one_pos
  refine ⟨K,l,Kp,?_⟩
  filter_upwards [priced,self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 from one_pos))] with r h rp small
  have hr:0<r:=rp
  have clear:ClearOf (0:E4) blank 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have apart:Injective (beside (sole (0:E4)) blank):=by
    intro i j _
    rcases i with i|i
    · rcases j with j|j
      · exact congr_arg Sum.inl (Subsingleton.elim i j)
      · exact Fin.elim0 j
    · exact Fin.elim0 i
  have reading:=h _ _ _ (room r rp) clear apart none
  rw [unselected_view,literal d v hr] at reading
  have grade:weight (fun _:Unit⊕Unit=>d) = ((2*d:ℕ):ℝ):=by simp [weight,Nat.cast_mul]
  rw [grade,Real.rpow_neg hr.le,Real.rpow_natCast] at reading
  have budget: r^(2*d)*‖OPE.Levy.pair d S (r • detectors) v (bar F d v)‖ ≤ K*badge r^l := by
    calc
      _ ≤ r^(2*d) * (K*badge r^l*(r^(2*d))⁻¹) :=mul_le_mul_of_nonneg_left reading (pow_nonneg hr.le _)
      _ = _ := by field_simp
  have raw:0≤badge r ∧ badge r≤dock r:=by
    unfold badge OPE.run dock LogV;rw [Real.log_inv];constructor <;> linarith [Real.log_nonpos hr.le small]
  exact budget.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ raw.1 raw.2 _) Kp)

include run in
theorem original (clock:Coupling G θ) (d:ℕ) (v:S.Field d):
    ∃ (K:ℝ) (l:ℕ),0≤K ∧ ∀ᶠr:ℝ in trail, ‖(r:ℂ)^d • (pub r d).symm v‖ ≤ K/(θ r)^l := by
  obtain ⟨A,Ap,gram⟩:=WilsonOrdinaryNestedInputGram.original run Z d
  obtain ⟨K,l,Kp,physical⟩:=reflected run d v
  obtain ⟨B,Bp,clocked⟩:=WilsonThermometerWeakPairNumeric.tariff simple θ clock l
  refine ⟨(1+A*K)*B,2*l,by positivity,?_⟩
  filter_upwards [gram,physical,clocked,self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 from one_pos))] with r heard amount wage rp small
  have hr:0<r:=rp
  have one:1≤dock r^l:=one_le_pow₀ (dock_valid r ⟨hr,small⟩)
  let ν:=‖(r:ℂ)^d • (pub r d).symm v‖
  have square:ν^2≤ A*K*dock r^l:=by
    change ‖(r:ℂ)^d • (pub r d).symm v‖^2≤_
    rw [norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,mul_pow,←pow_mul,Nat.mul_comm d 2]
    calc
      _ ≤ r^(2*d)*(A*‖OPE.Levy.pair d S (r • detectors) v (bar F d v)‖):=
        mul_le_mul_of_nonneg_left (heard v) (pow_nonneg hr.le _)
      _ = A*(r^(2*d)*‖OPE.Levy.pair d S (r • detectors) v (bar F d v)‖):=by ring
      _ ≤ A*(K*dock r^l):=mul_le_mul_of_nonneg_left amount Ap.le
      _ = _:=by ring
  calc
    ν ≤ 1+ν^2:=by nlinarith [sq_nonneg (ν-1/2)]
    _ ≤ (1+A*K)*dock r^l:=by nlinarith
    _ ≤ (1+A*K)*(B/θ r^(2*l)):=mul_le_mul_of_nonneg_left wage (by positivity)
    _ = _:=by ring
end YM.Integration.WilsonOrdinaryNestedInput
