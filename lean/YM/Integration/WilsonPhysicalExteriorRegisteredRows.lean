import YM.Integration.WilsonPhysicalExteriorFeeShift
import YM.Integration.MSFilteredWordReadout

/-! Each subtraction argument in a mixed finite Wilson report is allowed
to change independently. The response is reexpressed in the genuinely
normalized finite rows of the same preselected prescription; engineering
factors of every original measured field remain visible. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRegisteredRows
open Finset Matrix Lattice Labels Source Precision MS MS.Land MS.Menus MS.Rake
open RegulatorIR RegulatorIR.FVAAlt2 FVAAlt2 FVAAlt2.Lobby FVAAlt2.Billing
open WilsonPhysicalExteriorFeeShift MSFeeCoordinates
open PowerSeries (C)
open scoped Topology BigOperators Classical
variable {G:Gauge}{V:Frames G}{H:Hol G}{B:MS.Local.Physical.Deck G}{n:Side}
variable {W:Type} [LinearOrder W] [Fintype W]
variable (D:ChartRatio G)(R:Registry V H)(Q:Prescription B)
local notation "PS" => PowerSeries ℂ
abbrev Array (B:MS.Local.Physical.Deck G) (d:W→ℕ) := (i:W)→ Glyph B (d i)

private def attach (d:W→ℕ) : Array B d ≃ MSFeeReadout.Slots B d univ where
  toFun a i:=a i.val
  invFun a i:=a ⟨i,mem_univ i⟩
  left_inv _:=rfl
  right_inv _:=rfl

private theorem attached (d:W→ℕ) (z:(i:W)→ Glyph B (d i)→PS) (F:Array B d→PS) :
    (∑a:Array B d,(∏ i:W,z i (a i))*F a)=
    ∑a:MSFeeReadout.Slots B d univ,(∏i:(univ:Finset W),z i.val (a i))*F ((attach d).symm a) := by
  rw [←Equiv.sum_comp (attach d) (fun a => (∏i:(univ:Finset W),z i.val (a i))*F ((attach d).symm a))]
  refine sum_congr rfl fun a _=>?_
  simp only [Equiv.symm_apply_apply]
  change (∏i:W,z i (a i))*F a=(∏i:(univ:Finset W),z i.val (a i.val))*F a
  exact congrArg (fun w:PS=>w*F a)
    (Finset.prod_coe_sort (s:=(Finset.univ:Finset W)) (f:=fun i:W=>z i (a i))).symm

def field (y:ℝ) (x:W→Site n) (d:W→ℕ) (a:Array B d) : PS :=
  redo Q.team y (WilsonPoint D R n x (fun i=>owner (a i)))

def padded (y:ℝ) (x:W→Site n) (d:W→ℕ) (a:Array B d) : PS :=
  ∑ b:Array B d,(∏i:W,frame Q (d i) y (a i) (b i))*field D R Q y x d b

theorem sourced (y:ℝ) (x:W→Site n) (d:W→ℕ) (a:Array B d) :
    padded D R Q y x d a=prepare D R Q y (fun i=>owner (a i)) n x := by
  let e:W→ℕ:=fun i=>(a i).size
  let le (i:W): e i≤d i:=remaining (a i)
  let v:(i:W)→ Glyph B (d i)→PS:=fun i b=>frame Q (d i) y (a i) b
  let w:(i:W)→ Glyph B (e i)→PS:=fun i b=>fee Q (owner (a i)) y b
  let F:=field D R Q y x d
  let X:=field D R Q y x e
  change (∑ b:Array B d,(∏i:W,v i (b i))*F b) =
    ∑ b:Array B e,(∏ i:W,w i (b i))*X b
  rw [attached d v F,attached e w X]
  have pad:=MSFilteredWordReadout.sum_extend (A:=B) e d univ le
    (fun i=>v i.val) (fun b=>F ((attach d).symm b))
    (fun i b too=>outside Q y (a i.val) b too)
  rw [pad]
  refine sum_congr rfl fun b _=>?_
  have hw (i:(univ:Finset W)) :
      v i.val (extend (le i.val) (b i))=w i.val (b i):=WilsonPhysicalExteriorFeeShift.padded Q y _ _
  simp only [hw]
  rfl

private theorem linear (p:W→Label B) (y:ℝ) (v:W→ℝ) (x:W→Site n) :
    WilsonPhysicalExteriorSlotReference.original D R Q p y v x=
      ∑ a:Array B (fun i=>(p i).h),
        (∏i:W, change Q (p i).h (v i) y (Land.read (p i).item) (a i))*
        padded D R Q y x (fun i=>(p i).h) a := by
  let d:W→ℕ:=fun i=>(p i).h
  let U:(i:W)→ Glyph B (d i)→PS:=fun i a=>change Q (d i) (v i) y (Land.read (p i).item) a
  have hf (i:W) (b:Glyph B (d i)):
      bore p Q (v i) i b=∑ a,U i a*frame Q (d i) y a b :=(held Q _ _ _ _).symm
  unfold WilsonPhysicalExteriorSlotReference.original padded
  simp_rw [hf,Fintype.prod_sum,Finset.sum_mul,Finset.prod_mul_distrib,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  rfl

/-- The finite receiving coefficients at the original spacing. The changed
slot i may contribute a lower engineering dimension; its complete weight
is retained in the corresponding term of the sum. -/
theorem measured (p:W→Label B) (y:ℝ) (v eps:W→ℝ) (e:ℝ) (x:W→Site n)
    (ok:∀i,eps i≠0) (he:e≠0) :
    WilsonPhysicalExteriorSlotReference.report D R Q p y v eps x =
      ∑ a:Array B (fun i=>(p i).h),
        (∏ i:W, C (((eps i:ℂ)⁻¹)^(p i).h*(e:ℂ)^(a i).size)*
          change Q (p i).h (v i) y (Land.read (p i).item) (a i)) *
        newEra D R Q y (fun i=>owner (a i)) x e := by
  rw [WilsonPhysicalExteriorSlotReference.factored D R Q p y v eps x ok,linear D R Q p y v x,Finset.mul_sum]
  refine sum_congr rfl fun a _=>?_
  rw [sourced,tot_cost D R Q y (fun i=>owner (a i)) x e he,Finset.prod_mul_distrib]
  have h₀:(e:ℂ)≠0 := Complex.ofReal_ne_zero.mpr he
  have hc : (∏ i:W,C (((eps i:ℂ)⁻¹)^(p i).h*(e:ℂ)^(a i).size)) *
      C (((e:ℂ)⁻¹)^wt (fun i=>owner (a i)))=C (WilsonPhysicalExteriorSlotReference.engineering eps p) := by
    rw [←map_prod,←map_mul,WilsonPhysicalExteriorSlotReference.engineering,wt,
      ←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
    congr 1;refine prod_congr rfl fun i _=>?_
    change (_*(e:ℂ)^(a i).size)*((e:ℂ)⁻¹)^(a i).size=_
    rw [mul_assoc,←mul_pow,mul_inv_cancel₀ h₀,one_pow,mul_one]
  rw [←hc]
  ring

end YM.Integration.WilsonPhysicalExteriorRegisteredRows
end
