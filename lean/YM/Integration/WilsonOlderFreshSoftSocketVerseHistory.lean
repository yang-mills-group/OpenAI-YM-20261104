import YM.Integration.WilsonOlderFreshSoftSocketVerseSeed

/-! A complete signed fitted section run on one prior through every original kinetic reset. -/
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketVerseHistory
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
variable {G:Gauge}{D d:ℕ}(R:Run G)(W:Initialize G)
local notation "F" => R.family.labels.level d

theorem changeOfInput (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    {v K N k:ℕ}(vk:v≤K)(kn:K≤N)(X Y:Era G ℝ)(hx:Auth k X)(hy:Auth k Y):
    cruises L O N k K v (X-Y)=cruises L O N k K v X-cruises L O N k K v Y:=by
  let field:Fin 2→Era G ℝ:=![X,Y]
  let cash:Fin 2→ℝ:=![1,-1]
  have valid (a:Fin 2)(_ha:a∈(univ:Finset (Fin 2))):Auth k (field a):=by
    fin_cases a
    · exact hx
    · exact hy
  simpa [Fin.sum_univ_two,field,cash,sub_eq_add_neg] using
    WilsonIndependentCollarWeightedCruise.original L O simple ratio vk kn univ cash field valid

theorem original (s:Bool)(fit:d<D)(e:ℕ):
    ∃A:Alma F→ℝ,(∀a,0≤A a) ∧
    ∀(V:Realm G (e+1) Credit.leanC),Dormitory V d 0 Credit.leanC →
    ∀N K v:ℕ,V.anchor≤v → v≤K → K≤N → ∀z:ℝ,PadRank V v K z →
    ∀(x y:Verse F)(b:Volume D)(o:Cover),
    let L:=V.draws
    let O:=V.paid
    let field t:=planted R W s fit b t o
    let δ:=field (x-y)
    let fee:=‖ContinuousLinearMap.apply ℝ ℝ b‖*charge e (x-y) A
    let after t:=cruises L O N d K v (field t)
    after x-after y=cruises L O N d K v δ ∧
    ScalarTrim (after x-after y).2=clock L O N K v (ScalarTrim δ.2)+
      ∑i∈Ico v K,clock L O N i v (feed L O N d K i δ) ∧
    ∀j≤e,∀θ:ℝ,‖listen j θ (after x)-listen j θ (after y)‖≤
      (∑i∈range (j+1),|θ|^i)*((WilsonIndependentCollarOrdinaryWeak.price G d e).buy z*fee):=by
  classical
  obtain ⟨A,positive,income⟩:=WilsonOlderFreshSoftSocketVerseSeed.original R W s fit e
  refine ⟨A,positive,?_⟩
  intro V dorm N K v first vk kn z pad x y b o L O field δ fee after
  have eqδ:δ=field x-field y:=WilsonOlderFreshSoftSocketVerseSeed.linear R W s fit b x y o
  have active (t:Verse F):Auth d (field t):=WilsonIndependentMatchedOpeningFiled.enrolled R W s fit b t o
  obtain ⟨_,nn,input⟩:=income x y b o
  change Saturation e 0 0 (field x-field y).2 0 fee at input
  rw [←eqδ] at input
  have same:after x-after y=cruises L O N d K v δ:=by
    rw [eqδ,changeOfInput L O V.hG V.green vk kn _ _ (active x) (active y)]
  refine ⟨same,?_,?_⟩
  · rw [same]
    exact WilsonOlderFreshSoftRoseScalarLedger.original L O V.hG V.green N d K v vk kn δ (active _)
  · intro j je θ
    rw [←map_sub,same]
    let walk:Escort V v K (fun _=>0):=⟨first,vk,by intros;norm_num,by intros;norm_num,by intro i _ _;simp [thinLevel]⟩
    have hfee:0≤fee:=mul_nonneg (ContinuousLinearMap.apply ℝ ℝ b).opNorm_nonneg nn
    have atGrade (i:ℕ)(ie:i≤e):|(cruises L O N d K v δ).2 i 0 Fin.elim0|≤
        (WilsonIndependentCollarOrdinaryWeak.price G d e).buy z*fee:=by
      have paid:=(bulkCert G d e 0 Credit.leanC Credit.leanC).choose_spec i ie 0 V dorm v K _ N z walk
        pad kn δ fee (active _) hfee input
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

end YM.Integration.WilsonOlderFreshSoftSocketVerseHistory
