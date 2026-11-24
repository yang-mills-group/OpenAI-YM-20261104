import YM.Integration.WilsonPhysicalExteriorRegisteredRows
import YM.XSpace.FPS

/-! Two independently chosen bulk subtraction arguments on the very same
finite registered Wilson measurement. Revert the actual presold team's
old running variable before composing its new one. Both operations act
on the entire measured row, including all field fees. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRunningRows
open Finset Matrix Lattice Labels Source Precision MS MS.Land MS.Menus MS.Rake MS.Book MS.Book.Program
open RegulatorIR RegulatorIR.FVAAlt2 FVAAlt2 FVAAlt2.Lobby FVAAlt2.Billing
open WilsonPhysicalExteriorFeeShift WilsonPhysicalExteriorRegisteredRows
open PowerSeries (C coeff)
open scoped Topology BigOperators Classical
variable {G:Gauge}{V:Frames G}{H:Hol G}{B:MS.Local.Physical.Deck G}{n:Side}
variable {W:Type} [LinearOrder W] [Fintype W]
variable (D:ChartRatio G)(R:Registry V H)(Q:Prescription B)
local notation "PS" => PowerSeries ℂ

private theorem zero (P:Team) (y:ℝ) : PowerSeries.constantCoeff (shift P y)=0 :=
  (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm.trans (share P y)

private def inverse (P:Team) (y:ℝ) : PS :=
  (shift P y).substInvOfIsUnit (show IsUnit _ from (ann P y).symm ▸ isUnit_one)

private theorem inv_zero (P:Team) (y:ℝ) : PowerSeries.constantCoeff (inverse P y)=0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit ..

def first (P:Team) (y:ℝ) : PS →ₐ[ℂ] PS :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (zero P y))

def undo (P:Team) (y:ℝ) : PS →ₐ[ℂ] PS :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (inv_zero P y))

private theorem first_action (P:Team) (y:ℝ) (F:PS) : first P y F=F.subst (shift P y) :=
  congrFun (PowerSeries.coe_substAlgHom ..) F
private theorem undo_action (P:Team) (y:ℝ) (F:PS) : undo P y F=F.subst (inverse P y) :=
  congrFun (PowerSeries.coe_substAlgHom ..) F
private theorem lifts (P:Team) (y:ℝ) (F:PS) : undo P y (first P y F)=F := by
  rw [undo_action,first_action,PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (zero P y))
    (PowerSeries.HasSubst.of_constantCoeff_zero' (inv_zero P y)),inverse,
    PowerSeries.subst_substInvOfIsUnit_right _ (zero P y),PowerSeries.X_subst]

theorem evaluated (P:Team) (y:ℝ) (F:PS) : first P y F=Lobby.redo P y F := by
  apply PowerSeries.ext;intro k
  rw [first_action,XSpace.FPS.coeff_substituted F (zero P y)]
  change _=coeff k (PowerSeries.mk (Program.substitute (shift P y) (fun i=>coeff i F)))
  rw [PowerSeries.coeff_mk,Program.rules]
  refine Finset.sum_congr (by ext i;simp) fun i _=>?_
  change (coeff i F)*(coeff k ((shift P y)^i))=(coeff k ((shift P y)^i))*(coeff i F)
  exact mul_comm ..

def reprice (P:Team) (y z:ℝ) : PS →ₐ[ℂ] PS := (first P z).comp (undo P y)

theorem original (P:Team) (y z:ℝ) (F:PS) :
    reprice P y z (Lobby.redo P y F)=Lobby.redo P z F := by
  rw [←evaluated,←evaluated]
  change first P z (undo P y (first P y F))=_
  rw [lifts]

private theorem fixed (P:Team) (y z:ℝ) (a:ℂ): reprice P y z (C a)=C a :=
  (reprice P y z).commutes a

def coordinates (d:ℕ) (v y z:ℝ) : Matrix (Glyph B d) (Glyph B d) PS :=
  frame Q d v * (reprice Q.team y z).toRingHom.mapMatrix (oldFrame Q d y)

private theorem entry (p:Label B) (v y z:ℝ) (b:Glyph B p.h):
    ∑ a,coordinates Q p.h v y z (Land.read p.item) a * reprice Q.team y z (frame Q p.h y a b) =
      fee Q p v b := by
  let φ:PS →+* PS:=(reprice Q.team y z).toRingHom
  have old:oldFrame Q p.h y*frame Q p.h y=1:=by
    rw [oldFrame,WilsonPhysicalExteriorFeeShift.frame,←map_mul,Matrix.nonsing_inv_mul _ (MSFeeCoordinates.determinant Q p.h),map_one]
  have both:coordinates Q p.h v y z * φ.mapMatrix (frame Q p.h y)=frame Q p.h v:=by
    change (frame Q p.h v*φ.mapMatrix (oldFrame Q p.h y))*φ.mapMatrix (frame Q p.h y)=_
    rw [Matrix.mul_assoc,←map_mul,old,map_one,Matrix.mul_one]
  exact (congrFun (congrFun both (Land.read p.item)) b).trans
    (WilsonPhysicalExteriorFeeShift.padded Q v (Land.read p.item) b)

private theorem action (y z:ℝ) (x:W→Site n) (d:W→ℕ) (a:Array B d) :
    reprice Q.team y z (padded D R Q y x d a)=
    ∑ b:Array B d,(∏i:W,reprice Q.team y z (frame Q (d i) y (a i) (b i)))*
      field D R Q z x d b := by
  simp only [WilsonPhysicalExteriorRegisteredRows.padded,map_sum,map_mul,map_prod,field,original]

private theorem announced (p:W→Label B) (v:W→ℝ) (y z:ℝ) (x:W→Site n) :
    WilsonPhysicalExteriorSlotReference.original D R Q p z v x =
      ∑ a:Array B (fun i=>(p i).h),
        (∏i:W,coordinates Q (p i).h (v i) y z (Land.read (p i).item) (a i))*
          reprice Q.team y z (padded D R Q y x (fun i=>(p i).h) a) := by
  let d:W→ℕ:=fun i=>(p i).h
  let U:(i:W)→ Glyph B (d i)→PS:=fun i a=>coordinates Q (d i) (v i) y z (Land.read (p i).item) a
  have hf (i:W) (b:Glyph B (d i)) : bore p Q (v i) i b=
      ∑ a,U i a*reprice Q.team y z (frame Q (d i) y a b) := (entry Q _ _ _ _ _).symm
  unfold WilsonPhysicalExteriorSlotReference.original
  simp_rw [action,hf,Fintype.prod_sum,Finset.sum_mul,Finset.prod_mul_distrib,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  rfl

private theorem physical (r:W→Label B) (y z e:ℝ) (he:e≠0) (x:W→Site n) :
    C ((e:ℂ)^wt r)*reprice Q.team y z (newEra D R Q y r x e)=
      reprice Q.team y z (prepare D R Q y r n x) := by
  rw [tot_cost D R Q y r x e he,map_mul,fixed,←mul_assoc,←map_mul,←mul_pow,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr he),one_pow,map_one,one_mul]

/-- An exact finite all-word statement on the physical gauge regulator. The
complete old measured response is evaluated in the new genuine coupling;
no bound on the order of a Taylor truncation or spatial separation is used. -/
theorem measured (p:W→Label B) (v eps:W→ℝ) (y z e:ℝ) (x:W→Site n)
    (ok:∀i,eps i≠0) (he:e≠0) :
    WilsonPhysicalExteriorSlotReference.report D R Q p z v eps x =
      C (WilsonPhysicalExteriorSlotReference.engineering eps p)*
      ∑ a:Array B (fun i=>(p i).h),
        (∏ i:W,coordinates Q (p i).h (v i) y z (Land.read (p i).item) (a i))*
        (C ((e:ℂ)^wt (fun i=>owner (a i))) *
          reprice Q.team y z (newEra D R Q y (fun i=>owner (a i)) x e)) := by
  rw [WilsonPhysicalExteriorSlotReference.factored D R Q p z v eps x ok,announced D R Q p v y z x]
  congr 1
  refine sum_congr rfl fun a _=>?_
  rw [sourced,physical D R Q _ y z e he]

end YM.Integration.WilsonPhysicalExteriorRunningRows
end
