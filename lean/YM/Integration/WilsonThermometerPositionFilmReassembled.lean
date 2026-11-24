import YM.Integration.WilsonThermometerPositionFilmChartContact
import YM.Integration.WilsonThermometerPositionFilmDeposit

/-! Restore the complete ordinary incoming mark on this group field before the next integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmReassembled
open Function Finset RG Lattice Wilson Exterior Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Extra.Trajectories Primitives.GCC.Anchor
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Assembly
open RegulatorIR.FVAAlt2.Booth WilsonThermometerPositionFilmChartContact
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {R:Census V} {n:Side}
    (C:Bulk.Colors R G n) (s:R.Mode) (y:fieldDir G n 1)
local notation "a" => curve C.power (fun i=>Bulk.projected (C.mark i)) (1,y)

omit [Fintype V] in
private theorem marks (k:ℕ) : PowerSeries.coeff k a=Air.discharge C k y := by
  simp only [curve,PowerSeries.coeff_mk,Air.discharge,markLetter]

theorem original :
    flat C s 0 y=(Air.discharge C 0 y).pass.part s ∧
    flat C s 1 y=(Air.discharge C 1 y * (Air.discharge C 0 y).pass).part s := by
  let z:=series R 1 a
  have sym:Symmetric z:=⟨a,rfl⟩
  have blank:z.part (Board R 1).quiet=0:=mark_books C.power (fun i=>Bulk.projected (C.mark i)) (1,y) 1
  have full:=mark_exp (r:=1) (mark_curve_quiet C.power (fun i=>Bulk.projected (C.mark i)) (1,y))
  have ground:First.buc z=Air.discharge C 0 y:=(observation R 1 a (by decide : 0≤1)).trans (marks C y 0)
  have first:First.ind z=Air.discharge C 1 y:=(observation R 1 a (by decide : 1≤1)).trans (marks C y 1)
  constructor
  · change (PowerSeries.coeff 0 (markExp a)).part s=_
    rw [←observation R 1 (markExp a) (by decide : 0≤1),full]
    change (First.buc (Poly.pass z)).part s=_
    rw [First.buc_pass sym blank,ground]
  · change (PowerSeries.coeff 1 (markExp a)).part s=_
    rw [←observation R 1 (markExp a) (by decide : 1≤1),full]
    change (First.ind (Poly.pass z)).part s=_
    rw [First.ind_pass (by decide) sym blank,ground,first]

theorem deposited (y₀ y₁:Poly R) (one:y₀.part R.quiet=1) (zero:y₁.part R.quiet=0)
    (hot:∀b:Multi.Hot R,(Air.discharge C 0 y).part b.val=(connected y₀).part b.val ∧
      (Air.discharge C 1 y).part b.val=(y₁*inverseMass y₀).part b.val) :
    flat C s 0 y=y₀.part s ∧ flat C s 1 y=y₁.part s := by
  have same (k:Fin 2): Air.discharge C k.val y=if k=0 then connected y₀ else y₁*inverseMass y₀ := by
    apply Marker.Poly.ext
    intro h
    by_cases active:h.val.Nonempty
    · let b:Multi.Hot R:=⟨h,active⟩
      fin_cases k
      · exact (hot b).1
      · exact (hot b).2
    have eh:h=R.quiet:=Subtype.ext (not_nonempty_iff_eq_empty.mp active)
    subst h
    fin_cases k
    · rw [Air.discharge,part_lit_quiet]
      exact (connected_quiet one).symm
    · simp [Air.discharge,part_lit_quiet,Poly.quiet_mul,zero]
  have ground:Air.discharge C 0 y=connected y₀:=same 0
  have first:Air.discharge C 1 y=y₁*inverseMass y₀:=same 1
  have paid:=original C s y
  rw [first,ground,pass_connected one, mul_assoc,mul_comm (inverseMass y₀),right_inverse one,mul_one] at paid
  exact paid

theorem solitary {S:Census Unit} (L:Bulk.Colors S G n) (k:Fin 2) :
    flat L (S.fire ()) k.val y=
      Assembly.jet (Bulk.projected (L.mark (Arm.pub ()))) (L.power (Arm.pub ())+k.val) (1,y) := by
  let z:=curve L.power (fun i=>Bulk.projected (L.mark i)) (1,y)
  have seriesOne:markExp z=1+z:=by
    simp [markExp,Finset.sum_range_succ]
  change (PowerSeries.coeff k.val (markExp z)).part (S.fire ())=_
  rw [seriesOne,map_add]
  change (PowerSeries.coeff k.val (1:PTable S)).part (S.fire ())+(PowerSeries.coeff k.val z).part (S.fire ())=_
  have read:(PowerSeries.coeff k.val z).part (S.fire ())=
    Assembly.jet (Bulk.projected (L.mark (Arm.pub ()))) (L.power (Arm.pub ())+k.val) (1,y):=by
    rw [marks L y]
    exact Multi.part_lit _ (Arm.pub ())
  rw [read]
  fin_cases k <;> simp [Census.fire,Census.quiet,Subtype.ext_iff]

theorem faces {S:Census Unit} {Q:Type} [Fintype Q] (D:Q→Bulk.Colors S G n) (c:Q→ℂ)
    (Y:Fin 2→Poly R) (one:(Y 0).part R.quiet=1) (zero:(Y 1).part R.quiet=0)
    (links:∀h:Multi.Hot R,(Air.discharge C 0 y).part h.val=(connected (Y 0)).part h.val ∧
      (Air.discharge C 1 y).part h.val=(Y 1 * inverseMass (Y 0)).part h.val)
    (bought:∀b:Fin 2,(Y b).part s=∑q:Q,c q *
      Assembly.jet (Bulk.projected ((D q).mark (Arm.pub ()))) ((D q).power (Arm.pub ())+b.val) (1,y)) :
    ∀k:ℕ,k≤1→flat C s k y=∑q:Q,c q * flat (D q) (S.fire ()) k y := by
  have f:=deposited C s y (Y 0) (Y 1) one zero links
  have j (b:Fin 2):(Y b).part s=∑q:Q,c q * flat (D q) (S.fire ()) b.val y:=by
    rw [bought]
    apply Finset.sum_congr rfl
    intro q _
    rw [solitary y (D q) b]
  intro k hk
  interval_cases k
  · exact f.1.trans (j 0)
  · exact f.2.trans (j 1)

end YM.Integration.WilsonThermometerPositionFilmReassembled
