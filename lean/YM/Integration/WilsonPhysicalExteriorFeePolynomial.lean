import YM.Integration.WilsonPhysicalExteriorRunningRows
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-! Polynomial dependence on the three independent subtraction logs in the
*measured* matrix. The original inverse field register is already over
ℝ[X][[g]]; the inverse running variable is also taken over the polynomial
ring before any value of any of the three clocks is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFeePolynomial
open MS MS.Land MS.Menus MS.Book MS.Book.Program FVAAlt2
open WilsonPhysicalExteriorRunningRows
open scoped BigOperators Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}
local notation "K" => MvPolynomial (Fin 3) ℝ
local notation "PS" => PowerSeries ℂ

private def insert (i:Fin 3) : Polynomial ℝ →+* K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i)
private def atLogs (x:Fin 3→ℝ) : K →+* ℂ :=
  Complex.ofRealHom.comp (MvPolynomial.eval x)

private theorem at_insert (x:Fin 3→ℝ) (i:Fin 3) :
    (atLogs x).comp (insert i)=Complex.ofRealHom.comp (Polynomial.evalRingHom (x i)) := by
  apply Polynomial.ringHom_ext
  · intro r; simp [atLogs,insert]
  · simp [atLogs,insert]

private theorem scalar (x:Fin 3→ℝ) (i:Fin 3) (q:MSFeeCoordinates.R) :
    PowerSeries.map (atLogs x) (PowerSeries.map (insert i) q)=
      WilsonPhysicalExteriorFeeShift.scalar (x i) q := by
  apply PowerSeries.ext; intro n
  simp only [WilsonPhysicalExteriorFeeShift.scalar,MSFeeCoordinates.evaluate,
    RingHom.comp_apply,PowerSeries.coeff_map]
  exact DFunLike.congr_fun (at_insert x i) _

private def running (P:Team) (i:Fin 3) : PowerSeries K :=
  PowerSeries.mk (fun n=> if n=0 then 0 else if n=1 then 1 else insert i (P n).coupling)
private theorem base (P:Team) (i:Fin 3) : PowerSeries.constantCoeff (running P i)=0 := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [running]
private theorem leading (P:Team) (i:Fin 3) : PowerSeries.coeff 1 (running P i)=1 := by simp [running]
private def back (P:Team) (i:Fin 3) : PowerSeries K :=
  (running P i).substInvOfIsUnit (show IsUnit _ from (leading P i).symm ▸ isUnit_one)
private theorem book (P:Team) (i:Fin 3) (x:Fin 3→ℝ) :
    PowerSeries.map (atLogs x) (running P i)=shift P (x i) := by
  apply PowerSeries.ext;intro n
  by_cases h:n=0
  · simp [running,shift,h]
  by_cases h':n=1
  · simp [running,shift,h']
  simp only [PowerSeries.coeff_map,running,shift,PowerSeries.coeff_mk,if_neg h,if_neg h']
  exact DFunLike.congr_fun (at_insert x i) _

private theorem redo (P:Team) (y:ℝ) (a:PS) :
    Lobby.redo P y a=a.subst (shift P y) :=
  (WilsonPhysicalExteriorRunningRows.evaluated P y a).symm.trans (congrFun (PowerSeries.coe_substAlgHom ..) a)

private theorem sends (x:Fin 3→ℝ) (t a:PowerSeries K) (h:PowerSeries.constantCoeff t=0) :
    PowerSeries.map (atLogs x) (PowerSeries.subst t a) =
      PowerSeries.subst (PowerSeries.map (atLogs x) t) (PowerSeries.map (atLogs x) a) :=
  PowerSeries.map_subst (a:=t) (h:=atLogs x) (PowerSeries.HasSubst.of_constantCoeff_zero' h) a

private theorem returning (P:Team) (x:Fin 3→ℝ) (a:PowerSeries K) :
    Lobby.redo P (x 1) (PowerSeries.map (atLogs x) (a.subst (back P 1)))=
      PowerSeries.map (atLogs x) a := by
  rw [redo,←book P 1 x,←sends x _ _ (base P 1)]
  congr 1
  have hb:PowerSeries.constantCoeff (back P 1)=0:=by simp [back]
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hb)
    (PowerSeries.HasSubst.of_constantCoeff_zero' (base P 1)),back,
    PowerSeries.subst_substInvOfIsUnit_left _ (base P 1),PowerSeries.X_subst]

private theorem change (P:Team) (x:Fin 3→ℝ) (a:PowerSeries K) :
    PowerSeries.map (atLogs x) (PowerSeries.subst (running P 2) (PowerSeries.subst (back P 1) a)) =
      reprice P (x 1) (x 2) (PowerSeries.map (atLogs x) a) := by
  rw [sends x _ _ (base P 2),
    book,←redo,←WilsonPhysicalExteriorRunningRows.original P (x 1) (x 2),returning]

variable (Q:Prescription B)
def stored (d:ℕ) : Matrix (Glyph B d) (Glyph B d) (PowerSeries K) :=
  (PowerSeries.map (insert 0)).mapMatrix (MSFeeCoordinates.matrix Q d)*
    (show Matrix (Glyph B d) (Glyph B d) (PowerSeries K) from
      fun a b=>PowerSeries.subst (running Q.team 2) (PowerSeries.subst (back Q.team 1)
        (PowerSeries.map (insert 1) ((MSFeeCoordinates.matrix Q d)⁻¹ a b))))

theorem measured (d:ℕ) (x:Fin 3→ℝ) :
    (PowerSeries.map (atLogs x)).mapMatrix (stored Q d)=
      coordinates Q d (x 0) (x 1) (x 2) := by
  rw [stored,map_mul,coordinates];congr 1
  · apply Matrix.ext;intro a b;exact scalar x 0 _
  · apply Matrix.ext;intro a b
    exact (change Q.team x _).trans (congrArg (reprice Q.team (x 1) (x 2)) (scalar x 1 _))

/-- For the original Q, each perturbative order has one three-variable
polynomial before all field, old bulk and new bulk subtraction arguments. -/
theorem polynomial (d n:ℕ) (a b:Glyph B d) (x:Fin 3→ℝ) :
    PowerSeries.coeff n (coordinates Q d (x 0) (x 1) (x 2) a b) =
      ((MvPolynomial.eval x (PowerSeries.coeff n (stored Q d a b)):ℝ):ℂ) := by
  rw [←measured Q d x]
  change PowerSeries.coeff n (PowerSeries.map (atLogs x) (stored Q d a b)) =
    atLogs x (PowerSeries.coeff n (stored Q d a b))
  rw [PowerSeries.coeff_map]

end YM.Integration.WilsonPhysicalExteriorFeePolynomial
end
