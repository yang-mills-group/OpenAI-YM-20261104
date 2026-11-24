import YM.Integration.WilsonReportingPhysicalUnits
import YM.Integration.WilsonPositionSeparatedProfileOnePointMatched
import YM.Integration.WilsonPositionSeparatedProfileUnitMoment

/-! The complete original continuum correlation of an arbitrary ordered
list of subcritical fields, through separately dated measured changes at
their own dimensions, in every original state. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSubcriticalPhysicalCorrelations
open Function Filter Set Finset Table Spec OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Pert Pert.Position Lattice Maxwell Maxwell.Free XSpace XSpace.Normalize
open MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale RG17
open WilsonPositionSeparatedProfileOnePointMatched
open scoped Classical Topology BigOperators
variable {G : Gauge} (C : Family G)

theorem unit (d : ℕ) :
    (fields C.labels d).symm (leaf G d)=(Bel C.book).unit d := by
  apply address_inj C.labels d
  rw [address_eval,LinearEquiv.apply_symm_apply,unit_address]
  rfl

include C in
theorem scalar (simple : G.Simple) {d : ℕ} (low : d<4) (v : Sec G d) :
    ∃ c : ℂ, v=c • leaf G d := by
  obtain ⟨c,e⟩:=WilsonReportingPhysicalUnits.generated (C:=C) simple low ((fields C.labels d).symm v)
  refine ⟨c,(fields C.labels d).symm.injective ?_⟩
  rw [map_smul,unit,e]

theorem changed (d : ℕ) (a : Change G d) :
    adjusted C d a ((fields C.labels d).symm (leaf G d))=(fields C.labels d).symm (leaf G d) := by
  unfold WilsonPositionSeparatedProfileOnePointMatched.adjusted
  split_ifs with h
  · simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.ofBijective_apply,solitary]
  · rfl

theorem fixed (d : ℕ) (a : Change G d) :
    adjusted C d a ((Bel C.book).unit d)=(Bel C.book).unit d := by
  rw [←unit C d]
  exact changed C d a

private theorem tokens (T : Table C.book) (law : T.Basic) (n : ℕ) (d : Fin n→ℕ) :
    ∀x:Points n,x∈conf n→T.read x (fun i=>C.book.one (d i))=1 := by
  induction n with
  | zero=>intro x _; exact law.trivial ..
  | succ n ih=>
    intro x hx
    have roster : (fun i:Fin (n+1)=>C.book.one (d i))=
        Fin.cons (C.book.one (d 0)) (fun i:Fin n=>C.book.one (d i.succ)) := by
      funext i; exact Fin.cases rfl (fun _=>rfl) i
    rw [roster,law.unital hx]
    exact ih (fun i=>d i.succ) _ (Points.tail_in hx)

variable {C} {o : Extraction.Order} {U : Table C.book} (F : Final C o U) (J : ℝ→tower U)

theorem moment (p : Viewers F) {n : ℕ} (d : Fin n→ℕ) (x : Points n) (legal : x∈conf n) :
    U.classMoment (spectator F p) d x (fun i=>U.unit (d i))=1 := by
  let T:=spectator F p
  let law:=(spectate F p).laws
  have all:=U.at_project T law.toSymmetric (spectate_respects F p) legal (fun i=>C.book.one (d i))
  exact all.trans (tokens C T law n d x legal)

theorem observed (lead : Leading F J) {n : ℕ} (d : Fin n→ℕ) (a b : (i:Fin n)→ℝ→Change G (d i))
    (c : Fin n→ℂ) (φ : Test n) :
    ∀ᶠr in trail,∀p:Viewers F,
      φ.applyTo (fun x=>U.classMoment (spectator F p) d (r•x)
        (fun i=>J r (d i) (adjusted C (d i) (b i r) (adjusted C (d i) (a i r)
          ((fields C.labels (d i)).symm (c i • leaf G (d i))))))) =
        φ.applyTo (fun _=>∏i,c i) := by
  filter_upwards [Filter.eventually_all.mpr (fun i:Fin n=>lead.unit (d i)),RG17.positiveLength] with r units positive p
  apply φ.apply_eq
  intro x legal
  simp only [map_smul,unit,fixed,units]
  rw [MultilinearMap.map_smul_univ,moment F p d _ (Work.A05.smul_conf positive legal),smul_eq_mul,mul_one]

end YM.Integration.WilsonSubcriticalPhysicalCorrelations
