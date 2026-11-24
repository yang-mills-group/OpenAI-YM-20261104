import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingDebt
import YM.Integration.FVA1Physical.QLocalForced1026.Exterior
import YM.Push.LOCAL_SPLITTING.Budget

/-! Fund the full original signed packet on a crossing subseries, including
every admissible exterior companion and all scalar actors. The root of the
large actor may be unmarked. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Fusion.Attached
open Push.AbsoluteSums FVA1Physical.QLocalForced1026
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

private def chief (k:ℕ):Unit ↪ ℕ:=⟨fun _=>k,Function.injective_of_subsingleton _⟩
private theorem oneHead (k:ℕ):univ.map (chief k)={k}:=by
  ext i
  simp [chief]

abbrev seesLong (x:Site n)(D:ℕ)(S:Finset ℕ):Prop:=
  ∃i∈S,x∈(P.activities.forced i).support ∧ D≤coverNumber P.p.B (P.activities.forced i).support

private theorem one_invoice (w:V→ℝ)(wp:∀v,0<w v)(e:ℝ)(en:0≤e)
    (x:Site n)(D:ℕ)(S:Finset ℕ)(i:ℕ)(within:i∈S)
    (seen:x∈(P.activities.forced i).support)(long:D≤coverNumber P.p.B (P.activities.forced i).support)
    (t:T)(U:Config G n):
    Real.exp (e*D)*Poly.price w (packet P.activities P.p (A.K.hard t) U S)≤
      ownersCharge P.activities e 1 A.K w (fun _=>t) (fun _:Unit=>x) U (chief i) (S.erase i):=by
  let k:=fun j=>Poly.price w (A.K.hard t j U)
  let ex:=fun j=>Real.exp (e*coverNumber P.p.B (P.activities.forced j).support)
  have pn (j):0≤k j:=Poly.nonnegative wp _
  have large (j):1≤ex j:=Real.one_le_exp (mul_nonneg en (Nat.cast_nonneg _))
  have ep:Real.exp (e*D)≤ex i:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr long) en)
  have sides:Disjoint (univ.map (chief i)) (S.erase i):=by rw [oneHead];exact disjoint_singleton_left.mpr (notMem_erase i S)
  have restore:univ.map (chief i) ∪ S.erase i=S:=by rw [oneHead,singleton_union,insert_erase within]
  by_cases legal:P.activities.admissible P.p U S
  swap
  · rw [packet,if_neg legal,Poly.zero_price,mul_zero]
    exact ownersCharge_nonneg _ _ _ _ _ zero_le_one wp _ _ _ _ _
  have good:P.activities.admissible P.p U (univ.map (chief i)∪S.erase i):=by rw [restore];exact legal
  have tail:(∏j∈S.erase i,k j)≤∏j∈S.erase i,k j*ex j:=
    prod_le_prod (fun j _=>pn j) (fun j _=>le_mul_of_one_le_right (pn j) (large j))
  have main:=Poly.multiple wp S (fun j=>A.K.hard t j U)
  rw [packet,if_pos legal]
  apply (mul_le_mul_of_nonneg_left main (Real.exp_nonneg _)).trans
  change Real.exp (e*D)*(∏j∈S,k j)≤_
  rw [←Finset.mul_prod_erase S k within,←mul_assoc]
  have factor:Real.exp (e*D)*k i≤k i*ex i:=by rw [mul_comm _ (k i)];exact mul_le_mul_of_nonneg_left ep (pn i)
  exact (mul_le_mul factor tail (prod_nonneg fun j _=>pn j) (mul_nonneg (pn _) (Real.exp_nonneg _))).trans_eq (by
    dsimp only [ownersCharge]
    rw [Fintype.prod_unique]
    change k i*ex i*(∏ j∈S.erase i,k j*ex j) =
      (if x∈(P.activities.forced i).support then k i*ex i else 0) *
      (if Disjoint (univ.map (chief i)) (S.erase i) ∧
        P.activities.admissible P.p U (univ.map (chief i)∪S.erase i)
      then ∏ j∈S.erase i,1*(k j*ex j) else 0)
    rw [if_pos seen,if_pos ⟨sides,good⟩]
    simp only [one_mul])

/-- Price all the original rosters having ANY actual long actor through the
site, charged once per roster, with every other incident or distant actor
still present at the same field. No requirement that this owner carries a source. -/
theorem rooted_crossing_budget (w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)(paid:A.K.Paid w P.p.B e κ)
    (en:0≤e)(small:κ≤1)(x:Site n)(D:ℕ)(t:T)(U:Config G n):
    SumBudget (fun S:Finset ℕ=>if seesLong (P:=P) x D S
      then Real.exp (e*D)*Poly.price w (packet P.activities P.p (A.K.hard t) U S) else 0) κ:=by
  let yes:=fun S:Finset ℕ=>seesLong (P:=P) x D S
  let pred:=fun S:Finset ℕ=>if yes S then Real.exp (e*D)*
      Poly.price w (packet P.activities P.p (A.K.hard t) U S) else 0
  let active:=(S:Finset ℕ)→yes S → ℕ
  let pick:active:=fun _ h=>h.choose
  let key:=fun S:{S:Finset ℕ // yes S}=>(chief (pick S S.property),S.val.erase (pick S S.property))
  have picked (S:{S:Finset ℕ // yes S}):pick S S.property∈S.val ∧ x∈(P.activities.forced (pick S S.property)).support ∧
      D≤coverNumber P.p.B (P.activities.forced (pick S S.property)).support:=S.property.choose_spec
  have inject:Function.Injective key:=by
    intro S Q eq
    have idx:pick S S.property=pick Q Q.property:=congrArg (fun z:(Unit ↪ ℕ) × Finset ℕ=>z.1 ()) eq
    have rest:S.val.erase (pick S S.property)=Q.val.erase (pick Q Q.property):=congrArg Prod.snd eq
    apply Subtype.ext
    exact (insert_erase (picked S).1).symm.trans ((congrArg₂ insert idx rest).trans (insert_erase (picked Q).1))
  let fare:=fun z:(Unit ↪ ℕ) × Finset ℕ=>ownersCharge P.activities e 1 A.K w (fun _=>t)
    (fun _:Unit=>x) U z.1 z.2
  have bank:SumBudget fare κ:=by
    simpa only [fare,Fintype.card_unit,pow_one] using ownersCharge_budget P.activities e 1 A.K w wp paid
      zero_le_one (by simpa only [one_mul] using small) (fun _:Unit=>x) U (fun _ _=>t)
  have localBill:SumBudget (fun S:{S:Finset ℕ // yes S}=>pred S) κ:=by
    refine budget_mono (budget_pull key inject bank) (fun S=>?_) (fun S=>?_)
    · dsimp only [pred]
      rw [if_pos S.property]
      exact mul_nonneg (Real.exp_nonneg _) (Poly.nonnegative wp _)
    dsimp only [pred]
    rw [if_pos S.property]
    exact one_invoice A w wp e en x D S.val _ (picked S).1 (picked S).2.1 (picked S).2.2 t U
  refine Push.Local.sumBudget_pass (Function.Embedding.subtype yes) pred localBill ?_
  intro S absent
  exact if_neg fun h=>absent ⟨⟨S,h⟩,rfl⟩

/-- Fund the WHOLE crossed roster, including its vacuum component, all
separate inserted components, all additional flags and all admissible
companions, with no volume factor. Only the nominated touch set is charged.
The cover/touch input is required solely for active actors crossing the cut. -/
theorem crossed_cash_price (w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)(paid:A.K.Paid w P.p.B e κ)
    (en:0≤e)(small:κ≤1)(L F:Support n)(D:ℕ)(t:T)(U:Config G n)
    (tall:∀i,A.K.hard t i U≠0 → cross P.activities L i →
      D≤coverNumber P.p.B (P.activities.forced i).support ∧ ∃x∈F,x∈(P.activities.forced i).support):
    Poly.price w (crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L)≤
      Real.exp (-(e*D))*(F.card*κ):=by
  let η:=Real.exp (e*D)
  let raw:=packet P.activities P.p (A.K.hard t) U
  let yes:Set (Finset ℕ):={S|∃i∈S,cross P.activities L i}
  let terms:=yes.indicator raw
  let expenses:=fun x:Site n=>fun S:Finset ℕ=>if seesLong (P:=P) x D S then η*Poly.price w (raw S) else 0
  have localB (x:Site n):SumBudget (expenses x) κ:=rooted_crossing_budget A w wp e κ paid en small x D t U
  have house:SumBudget (fun S=>∑x∈F,expenses x S) (F.card*κ):=by
    simpa only [sum_const,nsmul_eq_mul] using budget_over F expenses (fun _=>κ) (fun x _=>localB x)
  have ep:0<η:=Real.exp_pos _
  have termB:SumBudget (fun S=>η*Poly.price w (terms S)) (F.card*κ):=by
    refine budget_mono house (fun S=>mul_nonneg ep.le (Poly.nonnegative wp _)) ?_
    intro S
    by_cases ok:S∈yes
    swap
    · dsimp only [terms]
      rw [Set.indicator_of_notMem ok,Poly.zero_price,mul_zero];exact house.1 _
    dsimp only [terms]
    rw [Set.indicator_of_mem ok]
    by_cases zero:raw S=0
    · rw [zero,Poly.zero_price,mul_zero];exact house.1 _
    obtain ⟨i,member,crosses⟩:=ok
    have active:A.K.hard t i U≠0:=by
      intro dead
      have gone:(∏ j∈S,A.K.hard t j U)=0:=prod_eq_zero member dead
      exact zero (by simp only [raw,packet,gone,ite_self])
    obtain ⟨big,x,localX,anchor⟩:=tall i active crosses
    have located:seesLong (P:=P) x D S:=⟨i,member,anchor,big⟩
    exact (show η*Poly.price w (raw S)=expenses x S from (if_pos located).symm).trans_le
      (single_le_sum (fun j _=>(localB j).1 S) localX)
  have inv:0≤η⁻¹:=inv_nonneg.mpr ep.le
  have unweighted:SumBudget (fun S=>Poly.price w (terms S)) (η⁻¹*(F.card*κ)):=by
    simpa only [←mul_assoc,inv_mul_cancel₀ ep.ne',one_mul] using budget_scale inv termB
  have total:Poly.price w (∑'S,terms S)≤η⁻¹*(F.card*κ):=
    (Poly.budgeted wp unweighted.2.1 (fun _=>le_rfl)).2.trans unweighted.2.2
  change Poly.price w (∑'S,terms S)≤_
  rw [Real.exp_neg]
  exact total

end YM.Integration.FVA1Physical.Exchange.RoseCut
