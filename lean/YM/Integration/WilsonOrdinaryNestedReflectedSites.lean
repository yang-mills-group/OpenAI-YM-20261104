import YM.Integration.WilsonOrdinaryNestedInputGram

/-! Place both genuine reflected arms at their actual two sites. Appending the
empty exterior only reindexes the same physical moment on the full table. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedReflectedSites
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


open Push.FiniteDetection.Free

open OPE.Levy
open private render submit transMap disk from YM.OPE.Levy.Inverse

abbrev pin (r:ℝ): Unit⊕Unit→E4 := render ((r • detectors).ofLp)
abbrev mark (d:ℕ) (v:S.Field d) : Labels S (fun _:Unit⊕Unit=>d) := submit d ![v,bar F d v]
def blank : Fin 0 → E4 := Fin.elim0
def voids : Labels S (fun _:Fin 0=>0) := Fin.elim0

theorem geometry : ∃ M η:ℝ, 0≤M ∧ 0<η ∧ ∀r:ℝ,0<r→WithinRoom r M η (pin r) 0 := by
  let x := detectors.ofLp
  let M := ‖x 0‖+‖x 1‖
  let η := ‖x 0-x 1‖
  have inj:Injective x := detectors_in
  have eta:0<η:=norm_sub_pos_iff.mpr (inj.ne (by decide))
  have top(i:Fin 2):‖x i‖≤M:=by
    fin_cases i
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have line (i j:Fin 2) (ne:i≠j): η=‖x i-x j‖:=by
    fin_cases i <;> fin_cases j
    · exact (ne rfl).elim
    · rfl
    · exact norm_sub_rev .. 
    · exact (ne rfl).elim
  refine ⟨M,η,add_nonneg (norm_nonneg _) (norm_nonneg _),eta,?_⟩
  intro r rp
  constructor
  · intro i
    change ‖r • x (transMap i)-0‖≤M*r
    rw [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos rp,mul_comm M r]
    exact mul_le_mul_of_nonneg_left (top _) rp.le
  · intro i j ne
    change η*r≤‖r • x (transMap i)-r • x (transMap j)‖
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos rp,mul_comm η r,line _ _ (transMap.injective.ne ne)]

theorem literal (d:ℕ) (v:S.Field d) {r:ℝ} (rp:0<r) :
    whole S (pin r) (mark (F:=F) d v) blank (voids (S:=S)) =
    OPE.Levy.pair d S (r • detectors) v (bar F d v) := by
  have inj : Injective (pin r) := by
    obtain ⟨M,η,_,ηp,geom⟩:=geometry
    intro i j eq
    by_contra ne
    have h := (geom r rp).spaced i j ne
    rw [eq,sub_self,norm_zero] at h
    exact (mul_pos ηp rp).not_ge h
  rw [whole_observed]
  have perm:=perm_observe S F.room.kernel.laws.toSymmetric (Equiv.sumEmpty (Unit⊕Unit) (Fin 0))
    (names (mark (F:=F) d v)) inj
  convert perm.trans (disk d (r • detectors).ofLp v (bar F d v)).symm using 2
  all_goals first | rfl | funext u;rcases u with u|u; rfl;exact Fin.elim0 u
end YM.Integration.WilsonOrdinaryNestedReflectedSites
