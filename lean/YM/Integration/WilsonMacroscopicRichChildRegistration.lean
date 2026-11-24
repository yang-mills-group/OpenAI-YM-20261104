import YM.Integration.IntrinsicProductLinearity
import YM.Integration.ReplicatedSignedCellBound

/-! The canonical counterterm for a jointly booked upper field has exactly its own
report. Incoming columns retain their independently tested fine positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichChildRegistration
open Lattice Wilson RG Source Trace.Physical.GermGraph RG16.Literal JointSignedInitialization
open scoped BigOperators Classical
variable {G : Gauge} (C : Family G) (H : C.Makes) {d N p : ℕ}
include H in
private theorem registered_credit (x : C.label d) {i : ℕ} (hp : C.ref d ≤ i) (hi : i ≤ N) :
    credit C N p d (C.O N p x 0) i hi =
      calValues d N p i ((C.factory d N p).terminal.symm x) := by
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [credit_bare C N p d H]
    funext U
    have issued := (H.calibrated d N p hp).encode ((C.factory d N p).terminal.symm x) U
    simpa only [Family.O, TransferData.cylinder, calValues, Trace.Physical.GermGraph.value,
      Pi.smul_apply, smul_eq_mul, mul_assoc] using issued.symm
  | of_succ i hi ih =>
    rw [credit_step C N p d _ (C.continuousO N p d x 0) hi,
      factory_eq (C := C) d N p i H hp hi, ih (hp.trans i.le_succ)]

theorem issued (z:C.label d) {b:ℕ}(ho:Opened C d b p)(live:b≤N) :
    Booked C N p d (C.O N p z 0) b live ∧
    topReport C N p d H b ho live (C.O N p z 0) = (C.factory d N p).terminal.symm z:=by
  let v:=(C.factory d N p).terminal.symm z
  have fee:=graph_cost (C:=C) d N p b H ho live v
  have balance:=registered_credit C H (p:=p) z ho.post live
  refine ⟨⟨_,_,fee,balance⟩,?_⟩
  unfold topReport
  rw [readPage_eq C N p d _ H live ho.post _ fee balance,
    ←fitting_apply (C:=C) d N p b H ho live v,LinearEquiv.symm_apply_apply]

def returned {b:ℕ}(ho:Opened C d b p)(live:b≤N)(Y:Cut C N p):C.label d:=
  (C.factory d N p).terminal (topReport C N p d H b ho live Y)

theorem null {b:ℕ}(ho:Opened C d b p)(live:b≤N)(Y:Cut C N p)(cY:Continuous Y)
    (book:Booked C N p d Y b live):
    let K:=C.O N p (returned C H ho live Y) 0
    Booked C N p d (Y-K) b live ∧ topReport C N p d H b ho live (Y-K)=0:=by
  intro K
  let A:Fin 2→Cut C N p:=![Y,K]
  let fee:Fin 2→ℂ:=![1,-1]
  obtain ⟨hK,reg⟩:=issued C H (returned C H ho live Y) ho live
  have ca:∀i,Continuous (A i):=by intro i;fin_cases i;exact cY;exact C.continuousO ..
  have admits:∀i,Booked C N p d (A i) b live:=by intro i;fin_cases i;exact book;exact hK
  have add:=IntrinsicProductLinearity.booked_sum C N p d b H ho live fee A ca admits
  have eq:(∑i,fee i • A i)=Y-K:=by simp [Fin.sum_univ_two,fee,A,sub_eq_add_neg]
  rw [eq] at add
  refine ⟨add.1,?_⟩
  rw [add.2]
  have regK : topReport C N p d H b ho live K = topReport C N p d H b ho live Y := by
    dsimp only [K]; rw [reg]; exact (C.factory d N p).terminal.symm_apply_apply _
  simp [A,fee,Fin.sum_univ_two,regK]

variable {I:Type*}[Fintype I]
def observed (d:I→ℕ)(v:(i:I)→C.label (d i))(roots:I→Finset (Site (C.side N p)))
    (φ:I→Site (C.side N p)→ℂ)(U:Config G (C.side N p)):ℂ:=
  ∏i,column C N p (d i) (v i) (roots i) (φ i) U

theorem original {h b:ℕ}(ho:Opened C h b p)(live:b≤N)(d:I→ℕ)(v:(i:I)→C.label (d i))
    (roots:I→Finset (Site (C.side N p)))(φ:I→Site (C.side N p)→ℂ)
    (book:Booked C N p h (observed C d v roots φ) b live):
    let Y:=observed C d v roots φ
    let K:=C.O N p (returned C H ho live Y) 0
    Booked C N p h (Y-K) b live ∧ topReport C N p h H b ho live (Y-K)=0:=by
  apply null C H ho live _ _ book
  exact continuous_finsetProd _ fun i _=>column_continuous C N p (d i) (v i) (roots i) (φ i)

end YM.Integration.WilsonMacroscopicRichChildRegistration
