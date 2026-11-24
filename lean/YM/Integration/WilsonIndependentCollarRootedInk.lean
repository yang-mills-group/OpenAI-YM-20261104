import YM.Integration.WilsonIndependentCollarRootedWidth

/-! Count every printed atom, derivative measure and relative position on
its originally held front, using the actual funded pointwise teacher. -/
set_option autoImplicit false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarRootedInk
open Function Finset Lattice RG Precision Wilson Exterior Work.F08 MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonIndependentCollarPrintIncome WilsonIndependentCollarRootedWidth
open scoped BigOperators Classical
variable {G:Gauge} {ι:Type} [DecidableEq ι] {D:ι→ℕ}

theorem original (I:Gear G)(σ:ℝ)(pos:0<σ)(paid:I.s=2*σ)(widths:Widths G)
    (k p h:ℕ)(hp:h≤p)(S:Finset ι)(v:ι)(front:v∈S)
    (P:(ι → Cover)→Era G (Pen D S))(auth:∀y,Auth k (P y))(A:ℝ)(salary:0≤A)
    (fund:∀y,∀i<p,∀r,Wig Bank.terrain y σ A S ((P y).2 i r))(o:Cover)(j:ℕ)(hj:j<h)(r:Fin (k+j+1)):
    let out:=issue widths p k I
    let t:=rooted S.card out.strip
    let bank:=packetH S P k h v o
    let Z:=fun c:Frill S v=>bank c j r
    ∃X:(u:Frill S v × RadP G r.val)→Stationary.Ink G r.val→Measure (Sky D),
      (∀u,Barn (Z u.1 u.2) (X u)) ∧ SumBudget
        (fun x:Frill S v × RadP G r.val=>
          Real.exp (t*feeH (toe S v o x.1) v S)*lease (Z x.1 x.2) (X x) t)
        (glacier G k h*(Real.exp (3*σ/8)*(out.fee*A))*sprigs S v (σ/2)):=by
  intro out t bank Z
  obtain ⟨openT,cap,span,_⟩:=WilsonIndependentCollarRootedWidth.original widths I σ pos paid p k S.card
  let C:=Real.exp (3*σ/8)*(out.fee*A)
  have hC:0≤C:=mul_nonneg (Real.exp_pos _).le (mul_nonneg (zero_le_one.trans out.funded) salary)
  let F (x:Frill S v):=Real.exp (-σ/8*realmSize S (toe S v o x))
  have held (x:Frill S v):tenure (bank x) S (toe S v o x) v h t (C*F x):=
    (WilsonIndependentCollarTeacherPrint.original I σ pos paid widths k p h hp (P _) (auth _) S
      (toe S v o x) v front A salary (fund _) t openT span cap).2.1
  choose M bound norm using fun x:Frill S v=>
    sparkle (bank x) (toe S v o x) v (held x) (mul_nonneg hC (Real.exp_pos _).le) j hj r
  let K:=glacier G k h*C
  let L (x: Frill S v × RadP G r.val):=
    Real.exp (t*feeH (toe S v o x.1) v S)*lease (Z x.1 x.2) (M x.1 x.2) t
  have byFront (i):SumBudget (fun a=>L (i,a)) (K*F i):=by
    unfold K;rw [mul_assoc];exact norm i
  have room:SumBudget F (sprigs S v (σ/2)):=by
    have wage:=sprigsPay front o (half_pos pos)
    have eq:-(σ/2)/4= -σ/8:=by ring
    simpa only [F,eq] using wage
  have package:=cap_scale room (show 0≤K from mul_nonneg (gentle ..) hC)
  have positive x:0≤L x:=(byFront x.1).1 x.2
  have all:Summable L:=(summable_prod_of_nonneg positive).mpr
    ⟨fun i=>(byFront i).2.1,Summable.of_nonneg_of_le (fun i=>tsum_nonneg fun j=>(byFront i).1 j)
      (fun i=>(byFront i).2.2) package.2.1⟩
  refine ⟨fun x=>M x.1 x.2,fun x=>bound x.1 x.2,positive,all,?_⟩
  change tsum L ≤ _
  rw [all.tsum_prod]
  exact (Summable.tsum_le_tsum (fun i=>(byFront i).2.2) all.prod package.2.1).trans package.2.2

end YM.Integration.WilsonIndependentCollarRootedInk
end
