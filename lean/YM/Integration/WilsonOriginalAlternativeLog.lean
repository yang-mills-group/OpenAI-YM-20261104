import YM.Integration.WilsonOriginalAlternativeLamps

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeLog
open Function Finset Set Lattice Wilson RG Ac Marker QuadraticLocal Push.Corrected Push.AbsoluteSums MeasureTheory
open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse WilsonOriginalAlternativeLamps
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {n:Side} {T I:Type} {o:V→Site n} {p:BudgetPoint}
variable (E:Lamps T I G p o R)

private theorem at_mode (s:(board R).Mode) (t:T) (U:Config G n) :
    (∑' i:roster E,((issued E).frame i t U).part s)=
      if ∀j∈s.val,j.2≠1 then ∑'i,(E.frame i t U).part (base R s) else 0 := by
  classical
  let f:((board R).Mode×I)→ℂ:=fun i=>if s=i.1 then E.light t i.2 U else 0
  let g:= (roster E).indicator f
  have sum:(∑' i:roster E,((issued E).frame i t U).part s)=∑' i,g i:=by
    change _=∑' i,(roster E).indicator f i
    rw [← _root_.tsum_subtype]
    exact tsum_congr fun i=>signal E i t U s
  have same:(∑' i:I,g (s,i))=∑' i,g i:=by
    apply Function.Injective.tsum_eq (g:=fun i:I=>(s,i)) (fun _ _ h=>congrArg Prod.snd h)
    intro q h
    by_contra off
    have no:s≠q.1:=fun h'=>off ⟨q.2,Prod.ext h' rfl⟩
    apply h
    simp [g,f,no,Set.indicator] 
  rw [sum,← same]
  split
  next active=>
    apply tsum_congr
    intro i
    by_cases use:base R s=E.mode i
    · have allowed:(s,i)∈roster E:=⟨use,active⟩
      change (roster E).indicator f (s,i)=(Poly.send (E.mode i) _).part _
      simp [Set.indicator_of_mem allowed,f,use]
    · have excluded:(s,i)∉roster E:=fun h=>use h.1
      change (roster E).indicator f (s,i)=(Poly.send (E.mode i) _).part _
      simp [Set.indicator_of_notMem excluded,use]
  next inactive=>
    have gone(i:I):g (s,i)=0:=Set.indicator_of_notMem (fun h: (s,i)∈roster E=>inactive h.2) _
    simp only [gone,tsum_zero]

theorem original {w:V→ℝ} (wp:∀i,0<w i) {B:ℕ} {a k:ℝ} (ha:0≤a)
    (fund:E.Paid w B a k) (t:T) (U:Config G n) :
    (issued E).log t U=inheritAll R (E.log t U) := by
  ext s
  rw [part]
  change (∑'i,(issued E).frame i t U).part s=_
  rw [Poly.share ((paid E wp fund).sums ha (positive R wp) t U),at_mode]
  split
  · exact (Poly.share (fund.sums ha wp t U) _).symm
  · rfl

end YM.Integration.WilsonOriginalAlternativeLog
