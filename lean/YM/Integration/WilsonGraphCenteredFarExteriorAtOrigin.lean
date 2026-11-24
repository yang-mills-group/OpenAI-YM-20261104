import YM.Integration.WilsonGraphCenteredFarTwoClocks

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedExteriorAtOrigin

open Function Filter Real PowerSeries Finset Continuation
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
  (H : Main.Match N simple M P true)
local notation "ψ" => GroupS.ψ N.criterion M (Teller.logNu 1)

include H in
/-- Compose the two complete field series with the full dimensional exterior at the original site. -/
theorem composed (h : ℕ) (x : Scale.Stage 2) (s : ℝ) (A B : Guard G h) (u v : Sec G h) :
    AppointedTwoClocks.pulled N h x (ψ (-s)) A B u v =
      AppointedBilinearCauchy.full N h (Facets.posing (-s) x)
        (Kseries N M h (-s) * A) (Kseries N M h (-s) * B) u v := by
  let T := Kseries N M h (-s)
  let W (k : Fin 2 → Dime G h) :=
    story (book N h 2 (Facets.posing (-s) x)) (fun i => dime G h (k i))
  have unfoldKernel (c : Fin 2 → Dime G h) :
      story (Program.substitute (ψ (-s)) (book N h 2 x)) (fun i => dime G h (c i)) =
        ∑ k : Fin 2 → Dime G h, (tax T (dime G h (c 0)) (k 0) *
          tax T (dime G h (c 1)) (k 1)) * W k := by
    have marks : (fun i => dime G h (c i)) = ![dime G h (c 0),dime G h (c 1)] := by
      funext i
      fin_cases i <;> rfl
    rw [marks]
    exact (AppointedBilinearCauchy.equivariant N M H h x (-s) _ _).symm
  unfold AppointedTwoClocks.pulled AppointedBilinearCauchy.full
  simp_rw [unfoldKernel, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  let z (i : Fin 2) (j : Dime G h) := tax T (dime G h j) (k i) * tax (![A,B] i) (![u,v] i) j
  calc
    _ = (∏ i : Fin 2, ∑ j : Dime G h, z i j) * W k := by
      rw [Fintype.prod_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      simp only [Fin.prod_univ_two, z, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    _ = _ := by
      rw [Fin.prod_univ_two, taxes, taxes]
      rfl

include H in
/-- The near-born center cancels its reverse field, leaving the authentic `−s` exterior on the spectator. -/
theorem mixed (h : ℕ) (x : Scale.Stage 2) (s : ℝ) (u v : Sec G h) :
    AppointedTwoClocks.pulled N h x (ψ (-s)) (AppointedCenteredReverse.reverseSeries N M h s) 1 u v =
      AppointedBilinearCauchy.full N h (Facets.posing (-s) x) 1 (Kseries N M h (-s)) u v := by
  rw [composed N M H, AppointedCenteredReverse.reverseIdentity N M H, mul_one]

end YM.FVA2.GradedFar.AppointedExteriorAtOrigin

