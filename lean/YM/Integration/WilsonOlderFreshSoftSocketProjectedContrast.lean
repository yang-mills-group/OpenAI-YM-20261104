import YM.Integration.WilsonOlderFreshSoftSocketProjectedSalary
import YM.Integration.WilsonPositionProgramTrialPublicOldReturn

/-! A single genuine public source projection on its own K-ancestral sites.
The complete thermal read includes the accumulated old scalar and every
positive-to-unit contribution before the independently chosen stopping date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketProjectedContrast
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


variable (R:Run G)(d:I→ℕ)
local notation "F" i:max => R.family.labels.level (d i)

def pivot (S:Finset I)(fill:∀i,(F i).Index)(b:∀i:S,(F i).Index)(i:I):(F i).Coeff:=
  Pi.single (key R d S fill b i) 1

omit [Fintype I] in
theorem isolated (S:Finset I)(fill:∀i,(F i).Index)(b q:∀i:S,(F i).Index):
    (∏i:S,amount R d (pivot R d S fill b) (fun _=>Complex.reCLM) i (q i))=if q=b then 1 else 0:=by
  classical
  have active (i:S):key R d S fill b i=b i:=dif_pos i.2
  by_cases same:q=b
  · subst q
    simp [amount,pivot,active]
  · rw [if_neg same]
    have apart:∃i,q i≠b i:=by
      by_contra! h
      exact same (funext h)
    obtain ⟨i,ne⟩:=apart
    exact prod_eq_zero (mem_univ i) (by simp [amount,pivot,active,Pi.single_eq_of_ne ne])

theorem original (W:Initialize G)(D:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)(e:ℕ):
    ∃B:ℝ,1≤B ∧ ∀S:Finset I,∀[Nonempty S],∃U W₀:Credit,
    ∀(V:Realm G (e+1) Credit.leanC),Dormitory V (mass d S) 0 Credit.leanC →
    ∀N K c w v:ℕ,V.anchor≤v → v≤w → w≤c → c≤K → K≤N →
    ∀z₀ z:ℝ,PadRank V c K z₀ → PadRank V v w z →
    ∀(κ:(i:I)→Knob (D i))(pt:I→Chamber)(routes:Digits V.draws I)(y:I → Cover)
      (fill:∀i,(F i).Index)(x x':∀i,(F i).Coeff)(φ φ':I→ℂ→L[ℝ]ℝ)(A:Case D),
    let L:=V.draws
    let O:=V.paid
    let f:=touch A S
    let P b:=material D d L O (stencil R D d (key R d S fill b) κ pt) N routes c K y S f
    let bill (ξ:∀i,(F i).Coeff)(phase:I→ℂ→L[ℝ]ℝ)(b:(i:S)→(F i).Index):=∏i:S,amount R d ξ phase i (b i)
    let diff b:=bill x φ b-bill x' φ' b
    let fare:=V.cash U w*V.tempC w c*((price G (mass d S) e).buy z₀*B^S.card)
    ∀j≤e,∀θ:ℝ,
    let measured (ξ:∀i,(F i).Coeff)(phase:I→ℂ→L[ℝ]ℝ):=
      flat (cruises L O N (mass d S) K v (columns R W D d cut κ pt (roots L routes (K-c) c y) S ξ phase A)) j θ
    let deposit b:=paidScalar L O N (mass d S) c w v (P b) j θ
    let left b:=flat (cruises L O N (mass d S) w v (axeR (front L O N (mass d S) c w (P b)))) j θ
    let residual:=measured x φ-measured x' φ' -∑b,diff b*deposit b
    residual=∑b,diff b*left b ∧
    ‖residual‖≤(∑b,‖diff b‖)*(‖f‖*((∑n∈range (j+1),|θ|^n)*(W₀.buy z*fare))):=by
  classical
  obtain ⟨B,bp,branch⟩:=WilsonOlderFreshSoftSocketProjectedSalary.original R W D d cut e
  refine ⟨B,bp,?_⟩
  intro S nonempty
  obtain ⟨U,W₀,offer⟩:=branch S
  refine ⟨U,W₀,?_⟩
  intro V dorm N K c w v first vw wc ck kn z₀ z early late κ pt routes y fill x x' φ φ' A
    L O f P bill diff fare j je θ measured deposit left residual
  let bound:=‖f‖*((∑n∈range (j+1),|θ|^n)*(W₀.buy z*fare))
  have heard (ξ:∀i,(F i).Coeff)(phase:I→ℂ→L[ℝ]ℝ):measured ξ phase=∑b,bill ξ phase b*(deposit b+left b):=
    WilsonOlderFreshSoftSocketPublicDose.original R W D d cut κ pt S fill ξ phase A L O V.hG V.green
      N routes v w c K vw wc ck kn y j θ
  have signed:residual=∑b,diff b*left b:=by
    change measured x φ-measured x' φ' -∑b,diff b*deposit b=_
    rw [heard,heard,←sum_sub_distrib,←sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    dsimp only [diff]
    ring
  refine ⟨signed,?_⟩
  have priceOne (b:(i:S)→(F i).Index):‖left b‖≤bound:=by
    let ξ:=pivot R d S fill b
    let π:=fun (_:I)=>Complex.reCLM
    have token (q:(i:S)→(F i).Index):bill ξ π q=if q=b then 1 else 0:=isolated R d S fill b q
    have weighted (a:((i:S)→(F i).Index)→ℝ):(∑q,bill ξ π q*a q)=a b:=by
      simp only [token,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,if_true]
    have size:(∑q,‖bill ξ π q‖)=1:=by
      simp only [token,apply_ite norm,norm_one,norm_zero,sum_ite_eq',mem_univ,if_true]
    have receipt:=offer V dorm N K c w v first vw wc ck kn z₀ z early late κ pt routes y fill ξ π A j je θ
    change ‖measured ξ π-∑q,bill ξ π q*deposit q‖≤(∑q,‖bill ξ π q‖)*bound at receipt
    rw [heard,weighted,weighted,add_sub_cancel_left,size,one_mul] at receipt
    exact receipt
  rw [signed,sum_mul]
  exact (norm_sum_le ..).trans (sum_le_sum (fun b _=>by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (priceOne b) (norm_nonneg _)))

end YM.Integration.WilsonOlderFreshSoftSocketProjectedContrast
end
