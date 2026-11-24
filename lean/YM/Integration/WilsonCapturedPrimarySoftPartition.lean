import YM.Integration.WilsonCapturedPrimarySoftRoster
import YM.Integration.WilsonCenteredSoftInventory
import YM.Comparison.RG02.Cumulants.Partition
/-! Every actual partition of an occupied ordinary response has a signed,
rooted inventory on the true ambient Wilson field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySoftPartition
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Push.Corrected Planned.GuardedAtom
open WilsonCenteredCaptureLampRoster WilsonCenteredCaptureRegularAtoms WilsonCapturedPrimarySoftRoster
open Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {P : Rep G n}

def index (q : (parts R).Mode) : Fin q.val.card ≃ ↥q.val :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card ↥q.val=q.val.card)).symm

def block (q : (parts R).Mode) (j : Fin q.val.card) := ((index q) j).val.val

def root (q : (parts R).Mode) (j : Fin q.val.card) : V := (((index q) j).val.property).choose

theorem seated (q : (parts R).Mode) (j : Fin q.val.card) : root q j∈(block q j).val :=
  (((index q) j).val.property).choose_spec

theorem inside {s : R.Mode} (q : (parts R).Mode) (admitted : q∈shards R s)
    (j : Fin q.val.card) : root q j∈s.val := by
  rw [←(mem_filter.mp admitted).2]
  exact mem_biUnion.mpr ⟨((index q) j).val,((index q) j).property,seated q j⟩

theorem enumerate (q : (parts R).Mode) (f : R.Mode→ℂ) :
    ∏ j,f (block q j)=∏ t∈q.val,f t.val := by
  have e := Equiv.prod_comp (index q) (fun t : ↥q.val=>f t.val.val)
  exact e.trans (Finset.prod_coe_sort q.val (fun t=>f t.val))

def tariff (p : BudgetPoint) (Z : Support n) (w : V→ℝ) (C : ℝ) (q : (parts R).Mode) : ℝ :=
  Real.exp ((p.supportExponent+2)*coverNumber p.B Z) * ∏ j,(Poly.toll w (block q j))⁻¹*C

private theorem fields {J : Type} (L : Lamps X ι G P.p o R) (x : X) (s : Finset J) (site : J→ι) (Z : Support n) :
    GaugeInvariant (viewed L s site x) ∧ Measurable (viewed L s site x) ∧
    UsesFinal P.p.threshold (domain L s site Z) (viewed L s site x) := by
  let T:=domain L s site Z
  have reg i (hi : i∈s) : Width.LocalCharge P.p o T (fun U=>L.frame (site i) x U) :=
    (QuadraticLocal.Shelter.Deck.locality (L:=L) x (site i)).widen (attends L s site Z hi)
  have full (i : J) (U : Config G n) : (L.frame (site i) x U).part (L.mode (site i)) = L.light x (site i) U := by
    simp [Lamps.frame,Poly.part_send]
  have meas : Measurable (viewed L s site x) := by
    change Measurable fun U=>∏ i∈s,L.light x (site i) U
    apply Finset.measurable_fun_prod
    intro i hi
    rw [←funext (full i)]
    exact (Poly.part_cont _).measurable.comp (reg i hi).borel
  have locals : UsesFinal P.p.threshold T (viewed L s site x) := by
    intro U V same fields
    apply prod_congr rfl
    intro i hi
    rw [←full i U,←full i V]
    exact congrArg (fun A : Poly R=>A.part (L.mode (site i))) ((reg i hi).reads U V same fields)
  have symmetry : GaugeInvariant (viewed L s site x) := by
    intro g U
    apply prod_congr rfl
    intro i hi
    rw [←full i _,←full i U]
    exact congrArg (fun A : Poly R=>A.part (L.mode (site i))) ((reg i hi).gauge g U)

  exact ⟨symmetry,meas,locals⟩

theorem original [Countable ι] (L : Lamps X ι G P.p o R) (x : X) (s : R.Mode)
    (q : (parts R).Mode) (admitted : q∈shards R s) (Z : Support n) (landing : ∀v∈s.val,o v∈Z)
    (w : V→ℝ) (hw : ∀v,0<w v) {C : ℝ} (paid : L.Paid w P.p.B (P.p.supportExponent+2) C) :
    Nonempty (WilsonCenteredSoftInventory.Receipt P Z (fun U=>∏ t∈q.val,(L.log x U).part t.val)
      (tariff P.p Z w C q)) := by
  have width : 0≤P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
  obtain ⟨e,pos,cap,cash⟩:=WilsonCapturedPrimarySoftRoster.original L (block q) (root q) (seated q)
    Z (fun j=>landing _ (inside q admitted j)) w hw width paid
  let T (r : Rows L (block q)) := domain L univ (fun j=>(r j).val) Z
  let f (r : Rows L (block q)) := viewed L univ (fun j=>(r j).val) x
  let amount (r : Rows L (block q)) := ∏ j,e (r j).val
  have localize (r : Rows L (block q)) := fields L x univ (fun j=>(r j).val) Z
  refine ⟨⟨Rows L (block q),inferInstance,T,f,amount,fun _ _ hy=>mem_union_left _ hy,
    fun r=>(localize r).1,fun r=>(localize r).2.1,fun r=>(localize r).2.2,
    fun r=>prod_nonneg fun j _=>pos (r j).val,?_,?_,?_⟩⟩
  · intro r U
    unfold f amount viewed
    rw [norm_prod]
    exact prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>L.light_size _ x U (cap _ x _ (L.address (r j).val).anchor))
  · change SumBudget (fun r : Rows L (block q)=>Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B (T r))*amount r) _
    rw [show (fun r : Rows L (block q)=>Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B (T r))*amount r) =
      (fun r=>amount r*Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B (T r))) from funext fun _=>mul_comm _ _]
    exact cash
  · intro U
    rw [←enumerate q (fun t=>(L.log x U).part t)]
    exact WilsonCapturedPrimarySoftRoster.complete L x (block q) U (paid.sums width hw x U)

end YM.Integration.WilsonCapturedPrimarySoftPartition
