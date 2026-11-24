import YM.Integration.WilsonOlderFreshSoftSocketProjectedContrast
import YM.Integration.WilsonPositionProgramTrialPublicOldReturn

/-! A single genuine public source projection on its own K-ancestral sites.
The complete thermal read includes the accumulated old scalar and every
positive-to-unit contribution before the independently chosen stopping date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketFullContrast
open Precision Function Finset Lattice Laurent Wilson RG Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Winding WilsonFiniteMarkedHistoryStep
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonPositionProgramTrialPublicPaidFace (amount key columns originalRow)
open WilsonReceivedDepositedVerseCensus (ordinary)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]


open WilsonOlderFreshSoftSocketSourceDeposits (paidScalar split)
open WilsonOlderFreshSoftOrdinary (material)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftRoseScalarLedger (front)
open WilsonOlderFreshSoftFigures (stencil)
open WilsonOlderFreshSoftSocketTotal (listen)
open WilsonOlderFreshHybridClock (flat)
open WilsonReceivedFixedDigitHistory (sound)
open WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil
open WilsonIndependentCollarRootedWidth


open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonOlderFreshSoftSocketRestored (stopped)
open WilsonOlderFreshSoftSocketHeard (during)
open WilsonIndependentCollarOrdinaryWeak (price)
open WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftSocketSourceDeposits (projected)



open WilsonIndependentCollarSeedTariff
open WilsonOlderFreshTerminalProgramme (series)
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Power
open WilsonIndependentCollarWeightedCruise
open WilsonPositionProgramTrialPublicPaidFace (originalRow)
open WilsonReceivedDepositedVerseCensus (ordinary)
variable (R:Run G)(d:I→ℕ)
local notation "F" i:max => R.family.labels.level (d i)

theorem original (W:Initialize G)(D:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)(e:ℕ):
    ∃B:ℝ,1≤B ∧ ∀S:Finset I,∀[Nonempty S],
    ∀(V:Realm G (e+1) Credit.leanC),Dormitory V (mass d S) 0 Credit.leanC →
    ∀N K v:ℕ,V.anchor≤v → v≤K → K≤N → ∀z:ℝ,PadRank V v K z →
    ∀(κ:(i:I)→Knob (D i))(pt:I→Chamber)(o:I → Cover)
      (fill:∀i,(F i).Index)(x x':∀i,(F i).Coeff)(φ φ':I→ℂ→L[ℝ]ℝ)(A:Case D),
    let L:=V.draws
    let O:=V.paid
    let f:=touch A S
    let bill (ξ:∀i,(F i).Coeff)(phase:I→ℂ→L[ℝ]ℝ)(b:(i:S)→(F i).Index):=∏i:S,amount R d ξ phase i (b i)
    let diff b:=bill x φ b-bill x' φ' b
    let fare:=(price G (mass d S) e).buy z*B^S.card
    ∀j≤e,∀θ:ℝ,
    let measured (ξ:∀i,(F i).Coeff)(phase:I→ℂ→L[ℝ]ℝ):=
      flat (cruises L O N (mass d S) K v (columns R W D d cut κ pt o S ξ phase A)) j θ
    let term b:=ordinary (stencil R D d (key R d S fill b) κ pt o) A S
    (measured x φ-measured x' φ'=∑b,diff b*flat (cruises L O N (mass d S) K v (term b)) j θ) ∧
    ‖measured x φ-measured x' φ'‖≤(∑b,‖diff b‖)*(‖f‖*((∑n∈range (j+1),|θ|^n)*fare)):=by
  classical
  obtain ⟨C,cp,stock⟩:=WilsonOlderFreshSoftFigures.original R D d e (w:=1) zero_lt_one
  obtain ⟨s,sp,openSeed⟩:=WilsonIndependentCollarSeedTariff.original G D d e
  refine ⟨s*C,one_le_mul_of_one_le_of_one_le sp cp,?_⟩
  intro S nonempty V dorm N K v first vk kn z pad κ pt o fill x x' φ φ' A L O f bill diff fare j je θ measured term
  let k:=mass d S
  let f₀:=‖f‖⁻¹ • f
  have recover:‖f‖ • f₀=f:=by
    by_cases zero:f=0
    · simp [zero,f₀]
    · have nz:‖f‖≠0:=(norm_ne_zero_iff (a:=f)).mpr zero
      simp [f₀,smul_smul,nz]
  have small:‖f₀‖≤1:=by
    by_cases zero:f=0
    · have vanish:f₀=0:=by simp [f₀,zero]
      rw [vanish,ContinuousLinearMap.opNorm_zero];norm_num
    · have pos:0<‖f‖:=(norm_pos_iff (a:=f)).mpr zero
      exact (ContinuousLinearMap.opNorm_smul_le _ _).trans (by
        change |‖f‖⁻¹| * ‖f‖≤1
        rw [abs_of_pos (inv_pos.mpr pos),inv_mul_cancel₀ pos.ne'])
  let Y (b:(i:S)→(F i).Index):=stencil R D d (key R d S fill b) κ pt
  have law (b:(i:S)→(F i).Index):Wellness d (Y b):=(stock (key R d S fill b) κ pt).1
  have active (b:(i:S)→(F i).Index):Auth k (levelsO (Y b o) S):=placedO _ ((law b).level' o) S
  have legal (b:(i:S)→(F i).Index):Auth k (term b):=(active b).tuft f
  have orig (ξ:∀i,(F i).Coeff)(phase:I→ℂ→L[ℝ]ℝ):
      measured ξ phase=∑b,bill ξ phase b*flat (cruises L O N k K v (term b)) j θ:=by
    change (listen j θ) (cruises L O N k K v (columns R W D d cut κ pt o S ξ phase A))=_
    rw [←WilsonPositionProgramTrialPublicPaidFace.original R W D d cut κ pt o S fill ξ phase A]
    unfold originalRow
    rw [WilsonIndependentCollarWeightedCruise.original L O V.hG V.green vk kn univ (bill ξ phase) term
      (fun b _=>legal b),map_sum]
    simp only [map_smul,smul_eq_mul]
    rfl
  have signed:measured x φ-measured x' φ'=∑b,diff b*flat (cruises L O N k K v (term b)) j θ:=by
    rw [orig,orig,←sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    exact (sub_mul ..).symm
  refine ⟨signed,?_⟩
  let walk:Escort V v K (fun _=>0):=⟨first,vk,by intros;norm_num,by intros;norm_num,by intro i _ _;simp [thinLevel]⟩
  have each (b:(i:S)→(F i).Index):
      ‖flat (cruises L O N k K v (term b)) j θ‖≤‖f‖*((∑n∈range (j+1),|θ|^n)*fare):=by
    let T:=tuftV f₀ (levelsO (Y b o) S)
    have input:=openSeed (Y b) (law b) C (zero_le_one.trans cp) (stock (key R d S fill b) κ pt).2
      o S (Finset.nonempty_coe_sort.mp nonempty) f₀ small
    have hired:Auth k T:=(active b).tuft f₀
    have h₀:0≤(s*C)^S.card:=pow_nonneg (mul_nonneg (zero_le_one.trans sp) (zero_le_one.trans cp)) _
    have per (i:ℕ)(ie:i≤e):|(cruises L O N k K v T).2 i 0 Fin.elim0|≤fare:=by
      have cash:=(bulkCert G k e 0 Credit.leanC Credit.leanC).choose_spec i ie 0 V dorm v K _ N z walk
        pad kn T ((s*C)^S.card) hired h₀ input
      have fee:=cash.2.1.sum_le_tsum ({Fin.elim0}:Finset (dock Cover _ 0)) (fun a _=>cash.1 a)
      rw [sum_singleton] at fee
      simpa only [hedge,autumn,pow_zero,one_mul,Real.norm_eq_abs] using fee.trans cash.2.2
    have summed:‖flat (cruises L O N k K v T) j θ‖≤(∑n∈range (j+1),|θ|^n)*fare:=by
      unfold flat series
      rw [sum_mul]
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro i hi
      rw [norm_mul,Real.norm_eq_abs,abs_pow,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (per i (by have h:=mem_range.mp hi;omega)) (pow_nonneg (abs_nonneg _) _)
    have scale:term b=‖f‖ • T:=by
      change tuftV f (levelsO (Y b o) S)=‖f‖ • tuftV f₀ (levelsO (Y b o) S)
      conv_lhs=>rw [←recover]
      apply Prod.ext
      · funext n r u a;rfl
      · funext n r a;rfl
    have move:cruises L O N k K v (‖f‖ • T)=‖f‖ • cruises L O N k K v T:=by
      simpa only [sum_singleton] using WilsonIndependentCollarWeightedCruise.original L O V.hG V.green vk kn
        ({()}:Finset Unit) (fun _=>‖f‖) (fun _=>T) (fun _ _=>hired)
    change ‖(listen j θ) (cruises L O N k K v (term b))‖≤_
    rw [scale,move,map_smul,smul_eq_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg f)]
    exact mul_le_mul_of_nonneg_left summed (norm_nonneg _)
  rw [signed,sum_mul]
  exact (norm_sum_le ..).trans (sum_le_sum (fun b _=>by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (each b) (norm_nonneg _)))

end YM.Integration.WilsonOlderFreshSoftSocketFullContrast
end
