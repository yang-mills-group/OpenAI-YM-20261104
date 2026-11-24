import YM.Integration.WilsonOlderFreshSoftSocketVerseProduct

/-! The measured quiet transports the entire difference of ordinary products and all of its scalar deposits. -/
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketVerseHearing
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel.Flooring
open PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedFiledIncome (charge)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonOlderFreshSoftSocketTotal (listen)
open WilsonOlderFreshSoftRoseScalarLedger (front feed)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators
open WilsonOlderFreshSoftSocketVerseProduct (Paid cost)
open WilsonIndependentMatchedRosterMasks (Bits choose quiet placed)
variable {G:Gauge}

def debit {n:ℕ}(e:ℕ)(d:Fin (n+1)→ℕ)(A B:Fin (n+1)→ℝ):ℝ:=
  ∑m∈(univ:Finset (Bits n)).erase (quiet n),cost e d (fun i=>if choose n m i then A i else B i)

def Heard {e:ℕ}(V:Realm G (e+1) Credit.leanC)(N K v d:ℕ)(X Y:Era G ℝ)(z fee:ℝ):Prop:=
  let L:=V.draws
  let O:=V.paid
  let δ:=X-Y
  let out:=cruises L O N d K v X-cruises L O N d K v Y
  out=cruises L O N d K v δ ∧
  ScalarTrim out.2=clock L O N K v (ScalarTrim δ.2)+
    ∑i∈Ico v K,clock L O N i v (feed L O N d K i δ) ∧
  ∀j≤e,∀θ:ℝ,‖listen j θ (cruises L O N d K v X)-listen j θ (cruises L O N d K v Y)‖≤
    (∑i∈range (j+1),|θ|^i)*((WilsonIndependentCollarOrdinaryWeak.price G d e).buy z*fee)

theorem paid {e d:ℕ}(V:Realm G (e+1) Credit.leanC)(dorm:Dormitory V d 0 Credit.leanC)
    {N K v:ℕ}(first:V.anchor≤v)(vk:v≤K)(kn:K≤N)(z:ℝ)(pad:PadRank V v K z)
    {X Y:Era G ℝ}{fee:ℝ}(hx:Auth d X)(hy:Auth d Y)(sale:Paid d e (X-Y) fee):
    Heard V N K v d X Y z fee:=by
  let L:=V.draws
  let O:=V.paid
  let δ:=X-Y
  let out:=cruises L O N d K v X-cruises L O N d K v Y
  have same:out=cruises L O N d K v δ:=(WilsonOlderFreshSoftSocketVerseHistory.changeOfInput L O V.hG V.green vk kn X Y hx hy).symm
  refine ⟨same,?_,?_⟩
  · change ScalarTrim out.2=_
    rw [same]
    exact WilsonOlderFreshSoftRoseScalarLedger.original L O V.hG V.green N d K v vk kn δ sale.1
  · intro j je θ
    rw [←map_sub]
    change ‖listen j θ out‖≤_
    rw [same]
    let walk:Escort V v K (fun _=>0):=⟨first,vk,by intros;norm_num,by intros;norm_num,by intro i _ _;simp [thinLevel]⟩
    have hfee:0≤fee:=sale.2.1
    have atGrade (i:ℕ)(ie:i≤e):|(cruises L O N d K v δ).2 i 0 Fin.elim0|≤
        (WilsonIndependentCollarOrdinaryWeak.price G d e).buy z*fee:=by
      have paid:=(bulkCert G d e 0 Credit.leanC Credit.leanC).choose_spec i ie 0 V dorm v K _ N z walk
        pad kn δ fee sale.1 hfee sale.2.2
      have cost:=paid.2.1.sum_le_tsum ({Fin.elim0}:Finset (dock Cover _ 0)) (fun a _=>paid.1 a)
      rw [sum_singleton] at cost
      simpa only [hedge,autumn,pow_zero,one_mul,Real.norm_eq_abs] using cost.trans paid.2.2
    change ‖∑i∈range (j+1),θ^i*(cruises L O N d K v δ).2 i 0 Fin.elim0‖≤_
    rw [sum_mul]
    apply (norm_sum_le ..).trans
    apply sum_le_sum
    intro i hi
    rw [norm_mul,Real.norm_eq_abs,abs_pow,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (atGrade i (by have h:=mem_range.mp hi;omega)) (pow_nonneg (abs_nonneg _) _)


theorem original {e n:ℕ}(d:Fin (n+1)→ℕ)(P Q:Fin (n+1)→Era G ℝ)(A B:Fin (n+1)→ℝ)
    (debits:∀i,Paid (d i) e (P i) (A i))(kept:∀i,Paid (d i) e (Q i) (B i))
    (V:Realm G (e+1) Credit.leanC)(dorm:Dormitory V (∑i,d i) 0 Credit.leanC)
    {N K v:ℕ}(first:V.anchor≤v)(vk:v≤K)(kn:K≤N)(z:ℝ)(pad:PadRank V v K z):
    Heard V N K v (∑i,d i) (MassP G ℝ n (fun i=>P i+Q i)) (MassP G ℝ n Q) z (debit e d A B):=by
  apply paid V dorm first vk kn z pad
  · exact manCo _ d (fun i=>(debits i).1.add (kept i).1)
  · exact manCo _ d (fun i=>(kept i).1)
  · exact (WilsonOlderFreshSoftSocketVerseProduct.signed d P Q A B debits kept).2

end YM.Integration.WilsonOlderFreshSoftSocketVerseHearing
