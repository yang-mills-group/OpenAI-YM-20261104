import YM.Integration.WilsonGraphCenteredFarEnteredRows
import YM.Integration.WilsonGraphCenteredFarHeaterSubstitution

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedBilinearCauchy

open Function Filter Real PowerSeries
open Register MS MS.Native MS.Menus MS.Tide MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
  (matchData : Main.Match N simple M P true)

/-- The full group correlation at the two positions, with a separately selected field series in each slot. -/
def full (h : ℕ) (x : Scale.Stage 2) (A B : Guard G h) (u v : Sec G h) : PowerSeries ℂ :=
  ∑ c : Fin 2 → Dime G h,
    (tax A u (c 0) * tax B v (c 1)) *
      story (book N h 2 x) (fun i => dime G h (c i))

/-- Each of the two near-born fields uses the same actual formal transport. -/
theorem both (h : ℕ) (x : Scale.Stage 2) (s : ℝ) (u v : Sec G h) :
    full N h x (Kseries N M h s) (Kseries N M h s) u v =
      story (status (Kseries N M h s) (book N h 2 x)) ![u,v] := by
  rw [estate, full]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A field already at the far scale contributes its constant basis coordinate. -/
theorem once (h : ℕ) (x : Scale.Stage 2) (s : ℝ) (u v : Sec G h) :
    full N h x (Kseries N M h s) 1 u v =
      ∑ c : Fin 2 → Dime G h, (tax (Kseries N M h s) u (c 0) *
        C ((dime G h).repr v (c 1))) * story (book N h 2 x) (fun i => dime G h (c i)) := by
  have unit (b : Dime G h) : tax (1 : Guard G h) v b = C ((dime G h).repr v b) := by
    refine PowerSeries.ext fun i => ?_
    simp only [tax, coeff_mk, coeff_one, coeff_C]
    split_ifs with hi
    · subst i; rfl
    · simp
  simp only [full, unit]

include matchData

/-- Full equivariance at every heat order and every separated two-point stage. -/
theorem equivariant (h : ℕ) (x : Scale.Stage 2) (s : ℝ) (u v : Sec G h) :
    full N h (Facets.posing s x) (Kseries N M h s) (Kseries N M h s) u v =
      story (Program.substitute (GroupS.ψ N.criterion M (Teller.logNu 1) s)
        (book N h 2 x)) ![u,v] := by
  rw [both]
  refine PowerSeries.ext fun k => ?_
  simp only [Reg.Point.story, coeff_mk]
  let B := GroupS.gaugeN N.scheme N.criterion M (Teller.logNu 1) s h
  have phase := (matchData.dilation (Teller.logNu 1)).check.reads s h
  have paid := congrArg (fun F : Scale.Way G h => F 2 x k ![u,v]) phase
  change status B (Facets.scaling s (book N h) 2 x) k ![u,v] =
    (Program.substitute (GroupS.ψ N.criterion M (Teller.logNu 1) s) (book N h 2 x)) k ![u,v] at paid
  rw [← paid, seen, seen]
  apply Finset.sum_congr rfl
  intro a _
  rw [Facets.scale_at]
  apply congrArg (book N h 2 (Facets.posing s x) (a none))
  funext i
  exact Kfactor (N:=N) (T:=M) s _

/-- Pull the clock back exactly once in each field slot that was born at the near scale. -/
theorem reverseField (h : ℕ) (s : ℝ) (u : Sec G h) (c : Dime G h) :
    tax (AppointedCenteredReverse.reverseSeries N M h s) u c =
      (tax (Kseries N M h s) u c).subst (GroupS.ψ N.criterion M (Teller.logNu 1) (-s)) :=
  Reg.Point.horizon _ _ _ _ ((matchData.dilation (Teller.logNu 1)).check.led (-s)).start

end YM.FVA2.GradedFar.AppointedBilinearCauchy
