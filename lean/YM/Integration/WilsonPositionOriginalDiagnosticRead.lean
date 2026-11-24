import YM.Integration.WilsonPositionOriginalDiagnosticSource
import YM.XSpace.KPos

/-! Each of the prescribed nested position diagnostics is a finite signed sum of
its enrolled Wilson film words. Its own decoder prices the error in a complete
field direction, including its lower-grade components. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticRead
open Function Finset Maxwell Maxwell.Free MS MS.Local.Physical MS.Menus MS.Theater
open XSpace XSpace.Normalize XSpace.Normalize.Fray PhysicalNext.Repeat.Legato
open WilsonPositionOriginalDiagnosticPanel
open scoped BigOperators Classical
variable {G:Gauge} (B:Deck G) {d:ℕ}

def weight (w:Window G d) (a:Fin w.n→Glyph B d) : ℂ :=
  ∏ j, (Daylight B d).repr (w.p j) (a j)

def reading (P:Prediction G d) (w:Window G d) (a:Fin w.n→Glyph B d) : ℂ :=
  P w.n w.t (fun j=>(Daylight B d) (a j))

theorem signed (w:Window G d) (P:Prediction G d) :
    watch w P = ∑ a:Fin w.n→Glyph B d, weight B w a * reading B P w a := by
  change (P w.n w.t) w.p=_
  have rows : w.p = fun j=>∑ b:Glyph B d, (Daylight B d).repr (w.p j) b • (Daylight B d) b :=
    funext fun j=>((Daylight B d).sum_repr (w.p j)).symm
  calc
    _ = (P w.n w.t) (fun j=>∑ b:Glyph B d, (Daylight B d).repr (w.p j) b • (Daylight B d) b) :=
      congrArg (P w.n w.t) rows
    _ = _ := by
      rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]
      exact sum_congr rfl fun a _=>(P w.n w.t).map_smul_univ ..

def receipt (S:Store G) (P:Prediction G d) (i:Fin (S.survey d).n) : ℂ :=
  ∑ a:Fin ((S.survey d).scope i).n→Glyph B d,
    weight B ((S.survey d).scope i) a * reading B P ((S.survey d).scope i) a

theorem measured (S:Store G) (P:Prediction G d) :
    (S.survey d).tally (receipt B S P)=(S.measure d).D P := by
  rw [←(S.survey d).equal]
  exact congrArg (S.survey d).tally (funext fun i=>(signed B _ P).symm)

theorem resolved (S:Store G) (T:Change G d) :
    (S.survey d).tally (receipt B S (gradient G d T))=T :=
  (measured B S _).trans ((S.prepared d).1 T)

def bill (w:Window G d) (P Q:Prediction G d) : ℝ :=
  ∑ a:Fin w.n→Glyph B d, ‖weight B w a‖ * ‖reading B P w a - reading B Q w a‖

theorem paid (S:Store G) (T:Change G d) (P:Prediction G d) :
    ‖guide G d (T-(S.measure d).D P)‖ ≤ ‖(S.survey d).stamps‖ *
      ∑ i:Fin (S.survey d).n, bill B ((S.survey d).scope i) (gradient G d T) P := by
  let f:=receipt B S (gradient G d T) - receipt B S P
  have h : (S.survey d).stamps f = guide G d (T-(S.measure d).D P) := by
    change guide G d ((S.survey d).tally _) = _
    rw [show (S.survey d).tally f = T-(S.measure d).D P by
      unfold f; rw [map_sub,resolved,measured]]
  rw [←h]
  apply ((S.survey d).stamps.le_opNorm f).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (sum_nonneg fun i _=>sum_nonneg fun a _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  apply le_trans _ (single_le_sum (f:=fun k=>bill B ((S.survey d).scope k) (gradient G d T) P)
    (fun k _=>sum_nonneg fun a _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mem_univ i))
  change ‖receipt B S (gradient G d T) i - receipt B S P i‖ ≤ _
  unfold receipt bill
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  exact sum_le_sum fun a _ => by rw [←mul_sub,norm_mul]

end YM.Integration.WilsonPositionOriginalDiagnosticRead
