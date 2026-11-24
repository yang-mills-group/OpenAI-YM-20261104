import YM.Integration.WilsonOrdinaryNestedPublic
import YM.Integration.WilsonPublicForkWallet
import YM.Integration.WilsonThermometerWeakPairNumeric

/-! The complete public output norm at a comparable vertex can pay its
relative grade-m signed coordinate with a fixed power of the local clock. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedOutput
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

include run in
theorem projected (m:ℕ) (c:Q.channels m) :
    ∃ (K:ℝ) (l:ℕ),0≤K ∧ ∀ᶠr in trail,∀v:RG17.Free R.family m,
      ‖ear F Q J Z r m c v‖ ≤ K * dock r^l * r^m * ‖v‖ := by
  let Lm:=WilsonCenteredNestedProjectedShadow.read F Q m m c
  have kill (e:ℕ) (em : e < m) (v:S.Field e) :
      Lm (F.sector.derivatives.rise (em.le.trans le_rfl) v)=0 := by
    change (Q.basis m).coord c ((Q.stratum m).subtype.leftInverse
      (Q.cutTest m m (F.sector.derivatives.rise em.le v)))=0
    rw [Q.cut_rise,Q.kills_lower _ _ em]
    simp
  obtain ⟨C,l,Cp,scalar⟩:=WilsonPublicForkWallet.coordinate F (simple:=simple) run.bliss run.matrix Lm le_rfl kill
  let B:=Module.finBasis ℂ (RG17.Free R.family m)
  have dues (i:Fin (Module.finrank ℂ (RG17.Free R.family m))) :
      ∃ W:ℝ,0≤W ∧ ∀ᶠr in trail,Ascent.cost F m r (pub r m (B i))≤W := by
    obtain ⟨W,Wp,here⟩:=WilsonNormalizedReflectedForm.uniform F J Z.store run.leading m
      (show 0≤‖B i‖+1 from by positivity)
    have converges:=WilsonPositionHomogeneousLeading.field F J Z run.leading run.obeys simple m (B i)
    refine ⟨W,Wp,?_⟩
    filter_upwards [here,converges.norm.eventually (ge_mem_nhds (lt_add_one _))] with r original bounded
    exact original false _ bounded
  choose W wp money using dues
  let K:= ∑i,‖(B.coord i).toContinuousLinearMap‖*W i
  have kp:0≤K:=Finset.sum_nonneg fun i _=>mul_nonneg (B.coord i).toContinuousLinearMap.opNorm_nonneg (wp i)
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  refine ⟨C*K,l,mul_nonneg Cp kp,?_⟩
  filter_upwards [eventually_all.mpr money,scalar,small,self_mem_nhdsWithin] with r paid quote small rp
  intro v
  have dk:0≤dock r:=zero_le_one.trans (dock_valid r ⟨rp,small⟩)
  let D:=C*dock r^l*r^m
  have dp:0≤D:=mul_nonneg (mul_nonneg Cp (pow_nonneg dk _)) (pow_nonneg rp.le _)
  have head (i:Fin (Module.finrank ℂ (RG17.Free R.family m))) :
      ‖ear F Q J Z r m c (B i)‖≤D*W i :=
    (quote _).trans (mul_le_mul_of_nonneg_left (paid i) dp)
  calc
    ‖ear F Q J Z r m c v‖ = ‖∑i,(B.coord i v) • ear F Q J Z r m c (B i)‖ := by
      unfold ear
      conv_lhs => rw [←B.sum_repr v]
      simp only [map_sum,map_smul,Module.Basis.coord_apply]
    _ ≤ ∑i,(D*‖v‖)*(‖(B.coord i).toContinuousLinearMap‖*W i) :=
      (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>by
        rw [norm_smul]
        refine (mul_le_mul ((B.coord i).toContinuousLinearMap.le_opNorm v) (head i) (norm_nonneg _) ?_).trans_eq ?_
        · positivity
        · ring)
    _ = (C*K)*dock r^l*r^m*‖v‖ := by rw [←Finset.mul_sum];dsimp [D,K];ring

include run in
theorem clocked (clock:Coupling G θ) (m:ℕ) (c:Q.channels m) :
    ∃ (l:ℕ) (K:ℝ),0≤K ∧ ∀ᶠr in trail,∀v:RG17.Free R.family m,
      ‖ear F Q J Z r m c v / (r:ℂ)^m‖ ≤ K/(θ r)^l*‖v‖ := by
  obtain ⟨B,j,Bp,raw⟩:=projected run Z m c
  obtain ⟨C,Cp,salary⟩:=WilsonThermometerWeakPairNumeric.tariff simple θ clock j
  refine ⟨2*j,B*C,mul_nonneg Bp Cp.le,?_⟩
  filter_upwards [raw,salary,self_mem_nhdsWithin] with r read fit rp v
  have pos : 0<r:=rp
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
  apply (div_le_iff₀ (pow_pos rp m)).mpr
  calc
    _ ≤ B*dock r^j*r^m*‖v‖:=read v
    _ ≤ B*(C/(θ r)^(2*j))*r^m*‖v‖:=by gcongr
    _ = _ := by ring

end YM.Integration.WilsonOrdinaryNestedOutput
