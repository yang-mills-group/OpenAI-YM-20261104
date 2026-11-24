import YM.PhysMS.Frame.Measured

/-! Finite unit rosters in each actual continuum state are the Wilson normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileUnitMoment
open Function Set Table Spec OPE OPE.Orbits Climb Trace.Pilot PhysMS
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S)

private theorem tokens (T : Table C.book) (law : T.Basic) (d n : ℕ) :
    ∀x:Points n,x∈conf n→T.read x (fun _=>C.book.one d)=1 := by
  induction n with
  | zero => intro x _; exact law.trivial .. 
  | succ n ih =>
      intro x hx
      have roster : (fun _:Fin (n+1)=>C.book.one d)=
          Fin.cons (C.book.one d) (fun _:Fin n=>C.book.one d) := by
        funext i; exact Fin.cases rfl (fun _=>rfl) i
      rw [roster,law.unital hx]
      exact ih _ (Points.tail_in hx)

theorem moment (p : Viewers F) (d : ℕ) {n : ℕ} (x : Points n) (legal : x∈conf n) :
    S.classMoment (spectator F p) (fun _=>d) x (fun _=>S.unit d)=1 := by
  let T:=spectator F p
  let law:=(spectate F p).laws
  let t (i : Fin n) := C.book.one d
  have first:=S.at_project T law.toSymmetric (spectate_respects F p) legal t
  exact first.trans (tokens (C:=C) T law d n x legal)

end YM.Integration.WilsonPositionSeparatedProfileUnitMoment
