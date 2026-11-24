import YM.Integration.WilsonMatrixTicketLanesConnectedReality
import YM.Integration.WilsonMatrixTicketLanesReportedSettlement

/-! The signed connected bare conditional of the two actual filed complex reporting columns. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedColumns
open Function Finset Lattice RG Wilson Tree Precision PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Parcel
open FVA2 RG12 RG17 Extraction Spec Table Pert.Asymptotics
open WilsonMatrixTicketLanesDescentWords WilsonMatrixTicketLanesReflectedGauge
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedSettlement
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) (L : RG17.Layout F)
abbrev BasisIndex (d : ℕ) := (R.family.labels.level d).Index

def degrees (d h : ℕ) : Unit⊕Unit→ℕ:=Sum.elim (fun _=>d) (fun _=>h)

def joined {C : Unit⊕Unit→Type} (a : C (.inl ())) (b : C (.inr ())) : ∀s,C s
  | .inl () => a
  | .inr () => b

private def unitEquiv (A : Type) : (Unit→A) ≃ A where
  toFun x:=x ()
  invFun a:=fun _=>a
  left_inv x:=by funext s;cases s;rfl
  right_inv _:=rfl

private def pairEquiv {C : Unit⊕Unit→Type} : (∀s,C s) ≃ C (.inl ()) × C (.inr ()) where
  toFun x:=(x (.inl ()),x (.inr ()))
  invFun y:=joined y.1 y.2
  left_inv x:=by funext s;rcases s with ⟨⟩|⟨⟩ <;> rfl
  right_inv _:=rfl

def single (r : ℝ) (d : ℕ) (w : R.family.label d) (b N p : ℕ) (date : L.level r=b+1)
    (u : Directions G (R.family.side b p)) (x : Site (R.family.side (L.level r) p)) : ℂ :=
  fresh R F L r (fun _ : Unit=>d) (fun _=>w) b N p date u (fun _=>x)

def joint (r : ℝ) (d h : ℕ) (w : R.family.label d) (v : R.family.label h) (b N p : ℕ) (date : L.level r=b+1)
    (u : Directions G (R.family.side b p)) (x y : Site (R.family.side (L.level r) p)) : ℂ :=
  fresh R F L r (degrees d h) (joined w v) b N p date u (Sum.elim (fun _=>x) (fun _=>y))

def weights (r : ℝ) (d : ℕ) (w : R.family.label d) (N p : ℕ) :=
  WilsonMatrixTicketLanesReportedMaster.color R d (L.level r) N p (L.shift d r w)

private theorem single_sum (r : ℝ) (d : ℕ) (w : R.family.label d) (b N p : ℕ) (date : L.level r=b+1)
    (upper : L.level r ≤ N) (age : R.family.ref d ≤ L.level r) (u : Directions G (R.family.side b p))
    (x : Site (R.family.side (L.level r) p)) :
    single R F L r d w b N p date u x = ∑ i : BasisIndex R d, weights R F L r d w N p i *
      reads (lamps R (fun _:Unit=>d) (fun _=>i)) (step R p date) u (fun _=>x) (regulatorRun R.family N p (L.level r)):=by
  letI : DecidableEq Unit:=fun a b=>Classical.propDecidable (a=b)
  apply (WilsonMatrixTicketLanesReportedOneBlock.original R F L r (fun _:Unit=>d) (fun _=>w) b N p date (fun _=>age) upper u (fun _=>x)).trans
  let A:=BasisIndex R d
  let c:=weights R F L r d w N p
  let total (j : Unit→A):=(∏ z : Unit,c (j z))*reads (lamps R (fun _:Unit=>d) j) (step R p date) u (fun _=>x) (regulatorRun R.family N p (L.level r))
  let point (j : A):=c j*reads (lamps R (fun _:Unit=>d) (fun _=>j)) (step R p date) u (fun _=>x) (regulatorRun R.family N p (L.level r))
  change ∑ z,total z = ∑ i,point i
  symm
  refine Fintype.sum_equiv (unitEquiv A).symm point total ?_
  intro i
  change _ = (∏ _ : Unit,c i)*_
  rw [Fintype.prod_unique]
  rfl


private theorem pair_sum (r : ℝ) (d h : ℕ) (w : R.family.label d) (v : R.family.label h) (b N p : ℕ) (date : L.level r=b+1)
    (upper : L.level r ≤ N) (age : R.family.ref d ≤ L.level r) (other : R.family.ref h ≤ L.level r)
    (u : Directions G (R.family.side b p)) (x y : Site (R.family.side (L.level r) p)) :
    joint R F L r d h w v b N p date u x y = ∑ i : BasisIndex R d, ∑ j : BasisIndex R h,
      (weights R F L r d w N p i * weights R F L r h v N p j) *
        reads (pair (lamps R (fun _:Unit=>d) (fun _=>i)) (lamps R (fun _:Unit=>h) (fun _=>j)))
          (step R p date) u (Sum.elim (fun _=>x) (fun _=>y)) (regulatorRun R.family N p (L.level r)):=by
  letI : DecidableEq (Unit⊕Unit):=fun a b=>Classical.propDecidable (a=b)
  let A:=degrees d h
  let C:=fun s=>BasisIndex R (A s)
  apply (WilsonMatrixTicketLanesReportedOneBlock.original R F L r A (joined w v) b N p date
    (by rintro (⟨⟩|⟨⟩);exact age;exact other) upper u (Sum.elim (fun _=>x) (fun _=>y))).trans
  let z:=fun i j=>(weights R F L r d w N p i * weights R F L r h v N p j)*
    reads (pair (lamps R (fun _:Unit=>d) (fun _=>i)) (lamps R (fun _:Unit=>h) (fun _=>j)))
      (step R p date) u (Sum.elim (fun _=>x) (fun _=>y)) (regulatorRun R.family N p (L.level r))
  let combined (t : BasisIndex R d × BasisIndex R h):=z t.1 t.2
  let total (t : ∀s,C s):=(∏s,WilsonMatrixTicketLanesReportedMaster.color R (A s) (L.level r) N p (L.shift (A s) r (joined (C:=fun t=>R.family.label (A t)) w v s)) (t s)) *
    reads (lamps R A t) (step R p date) u (Sum.elim (fun _=>x) (fun _=>y)) (regulatorRun R.family N p (L.level r))
  change ∑ t,total t = ∑ i,∑ j,z i j
  calc
    ∑ t,total t = ∑ ij,combined ij:=by
      symm
      refine Fintype.sum_equiv (pairEquiv (C:=C)).symm combined total ?_
      rintro ⟨i,j⟩
      dsimp only [combined,z,total]
      rw [Fintype.prod_sum_type,Fintype.prod_unique,Fintype.prod_unique]
      congr 1
    _ = _:=Fintype.sum_prod_type combined


/-- Both original singleton means are subtracted before estimating the actual signed complete sum. -/
theorem exact_sum (r : ℝ) (d h : ℕ) (w : R.family.label d) (v : R.family.label h) (b N p : ℕ) (date : L.level r=b+1)
    (upper : L.level r ≤ N) (age : R.family.ref d ≤ L.level r) (other : R.family.ref h ≤ L.level r)
    (u : Directions G (R.family.side b p)) (x y : Site (R.family.side (L.level r) p)) :
    joint R F L r d h w v b N p date u x y - single R F L r d w b N p date u x * single R F L r h v b N p date u y =
      ∑ i : BasisIndex R d, ∑ j : BasisIndex R h, (weights R F L r d w N p i * weights R F L r h v N p j) *
        (measured (step R p date) u R (fun _:Unit=>d) (fun _:Unit=>h) (fun _=>i) (fun _=>j)
          (fun _=>x) (fun _=>y) (regulatorRun R.family N p (L.level r)) : ℂ):=by
  rw [pair_sum R F L r d h w v b N p date upper age other u x y,
    single_sum R F L r d w b N p date upper age u x,single_sum R F L r h v b N p date upper other u y,
    sum_mul,←sum_sub_distrib]
  apply sum_congr rfl;intro i _
  rw [mul_sum,←sum_sub_distrib]
  apply sum_congr rfl;intro j _
  rw [←WilsonMatrixTicketLanesConnectedReality.covariance (step R p date) u R (fun _:Unit=>d) (fun _:Unit=>h)
    (fun _=>i) (fun _=>j) (fun _=>x) (fun _=>y) (regulatorRun R.family N p (L.level r))]
  ring

end YM.Integration.WilsonMatrixTicketLanesConnectedColumns
