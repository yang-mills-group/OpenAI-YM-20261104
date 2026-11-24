import YM.Integration.WilsonOlderFreshSoftSocketPublicDose
import YM.Integration.WilsonOlderFreshSoftSocketTest
import YM.Integration.WilsonIndependentCollarWeightedCruise
import YM.Integration.WilsonPositionProgramTrialPublicOldReturn

/-! A single genuine public source projection on its own K-ancestral sites.
The complete thermal read includes the accumulated old scalar and every
positive-to-unit contribution before the independently chosen stopping date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketProjectedSalary
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

private theorem axeScale (h:ℝ)(Q:Era G ℝ):axeR (h • Q)=h • axeR Q:=by
  apply Prod.ext
  · funext n r a b
    cases a <;> simp [axeR,lop,Pi.smul_apply,smul_eq_mul]
  · funext n r a
    cases r <;> simp [axeR,lop,Pi.smul_apply,smul_eq_mul]

private theorem cruiseScale (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    {N k w v:ℕ}(vw:v≤w)(wn:w≤N)(Q:Era G ℝ)(legal:Auth k Q)(s:ℝ):
    cruises L O N k w v (s • Q)=s • cruises L O N k w v Q:=by
  simpa only [Finset.sum_singleton] using WilsonIndependentCollarWeightedCruise.original L O simple ratio vw wn
    ({()}:Finset Unit) (fun _=>s) (fun _=>Q) (fun _ _=>legal)

theorem original (R:Run G)(W:Initialize G)(D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)(e:ℕ):
    ∃B:ℝ,1≤B ∧ ∀S:Finset I,∀[Nonempty S],∃U W₀:Credit,
    ∀(V:Realm G (e+1) Credit.leanC),Dormitory V (mass d S) 0 Credit.leanC →
    ∀N K c w v:ℕ,V.anchor≤v → v≤w → w≤c → c≤K → K≤N →
    ∀z₀ z:ℝ,PadRank V c K z₀ → PadRank V v w z →
    ∀(κ:(i:I)→Knob (D i))(pt:I→Chamber)(routes:Digits V.draws I)(y:I → Cover)
      (fill:∀i,(R.family.labels.level (d i)).Index)(x:∀i,(R.family.labels.level (d i)).Coeff)
      (φ:I→ℂ→L[ℝ]ℝ)(A:Case D),
    let L:=V.draws
    let O:=V.paid
    let f:=touch A S
    let source b:=material D d L O (stencil R D d (key R d S fill b) κ pt) N routes c K y S f
    let income (b:(i:S)→(R.family.labels.level (d i)).Index):=∏i:S,amount R d x φ i (b i)
    let fare:=V.cash U w*V.tempC w c*((price G (mass d S) e).buy z₀*B^S.card)
    ∀j≤e,∀θ:ℝ,
    ‖flat (cruises L O N (mass d S) K v (columns R W D d cut κ pt (roots L routes (K-c) c y) S x φ A)) j θ-
      ∑b,income b*paidScalar L O N (mass d S) c w v (source b) j θ‖≤
      (∑b,‖income b‖)*(‖f‖*((∑n∈range (j+1),|θ|^n)*(W₀.buy z*fare))):=by
  classical
  obtain ⟨C,cp,stock⟩:=WilsonOlderFreshSoftFigures.original R D d e (w:=1) zero_lt_one
  obtain ⟨B,bp,offer⟩:=WilsonOlderFreshSoftOrdinary.original G D d e
  refine ⟨B*C,one_le_mul_of_one_le_of_one_le bp cp,?_⟩
  intro S nonempty
  obtain ⟨U,W₀,pay⟩:=offer S (Finset.nonempty_coe_sort.mp nonempty)
  refine ⟨U,W₀,?_⟩
  intro V dorm N K c w v first vw wc ck kn z₀ z early late κ pt routes y fill x φ A L O f source income fare j je θ
  let t:=‖f‖
  let f₀:=t⁻¹ • f
  have tn:0≤t:=norm_nonneg f
  have recover:t • f₀=f:=by
    by_cases zero:f=0
    · simp [zero,f₀]
    · have nz:t≠0:=(norm_ne_zero_iff (a:=f)).mpr zero
      simp [f₀,smul_smul,nz]
  have small:‖f₀‖≤1:=by
    by_cases zero:f=0
    · have vanish:f₀=0:=by simp [f₀,zero]
      rw [vanish,ContinuousLinearMap.opNorm_zero];norm_num
    · have pos:0<t:=(norm_pos_iff (a:=f)).mpr zero
      exact (ContinuousLinearMap.opNorm_smul_le _ _).trans (by
        change |t⁻¹| * t≤1
        rw [abs_of_pos (inv_pos.mpr pos),inv_mul_cancel₀ pos.ne'])
  let result (b:(i:S)→(R.family.labels.level (d i)).Index):=
    flat (cruises L O N (mass d S) w v (axeR (front L O N (mass d S) c w (source b)))) j θ
  let bound:=(∑n∈range (j+1),|θ|^n)*(W₀.buy z*fare)
  have priceOne (b:(i:S)→(R.family.labels.level (d i)).Index):‖result b‖≤t*bound:=by
    let Y:=stencil R D d (key R d S fill b) κ pt
    let bank:=levelsO (itinerary L O d N routes (K-c) c Y y) S
    have law:Wellness d Y:=(stock (key R d S fill b) κ pt).1
    have counted:=sound L O d N routes V.hG V.green Y law (K-c) c (by omega)
    have legal:Auth (mass d S) bank:=placedO _ (counted.level' y) S
    let P:=material D d L O Y N routes c K y S f₀
    let H:=front L O N (mass d S) c w P
    have allocated:=pay V dorm N K c w v first vw wc ck kn z₀ z early late Y law
      C (zero_le_one.trans cp) (stock (key R d S fill b) κ pt).2 routes y f₀ small
    have hp:Auth (mass d S) P:=allocated.1
    have hh:Auth (mass d S) H:=cruising L V.hG V.green wc (ck.trans kn) hp
    have up:source b=t • P:=by
      change tuftV f bank=t • tuftV f₀ bank
      conv_lhs=>rw [←recover]
      apply Prod.ext
      · funext n r u a;rfl
      · funext n r a;rfl
    have bound₀:=allocated.2.2.2.2 j je θ
    have signed:=split L O V.hG V.green N (mass d S) c w v vw wc (ck.trans kn) P hp j θ
    rw [←projected L O V.hG V.green N (mass d S) c w v vw wc (ck.trans kn) P hp j θ] at signed
    change ‖(listen j θ) (cruises L O N (mass d S) w v (axeR (cruises L O N (mass d S) c w (source b))))‖≤t*bound
    rw [up,cruiseScale L O V.hG V.green wc (ck.trans kn) P hp t,axeScale]
    change ‖(listen j θ) (cruises L O N (mass d S) w v (t • axeR H))‖≤t*bound
    rw [cruiseScale L O V.hG V.green vw (wc.trans (ck.trans kn)) (axeR H) hh.axe t,map_smul,smul_eq_mul,
      norm_mul,Real.norm_eq_abs,abs_of_nonneg tn]
    have paidOne:‖flat (cruises L O N (mass d S) w v (axeR (front L O N (mass d S) c w P))) j θ‖≤bound:=by
      rw [←signed]
      exact bound₀
    exact mul_le_mul_of_nonneg_left paidOne tn
  have whole:=WilsonOlderFreshSoftSocketPublicDose.original R W D d cut κ pt S fill x φ A L O V.hG V.green
    N routes v w c K vw wc ck kn y j θ
  change _=∑b,income b*(paidScalar L O N (mass d S) c w v (source b) j θ+result b) at whole
  rw [whole]
  simp_rw [mul_add]
  rw [sum_add_distrib,add_sub_cancel_left]
  apply (norm_sum_le ..).trans
  rw [sum_mul]
  apply sum_le_sum
  intro b _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (priceOne b) (norm_nonneg _)

end YM.Integration.WilsonOlderFreshSoftSocketProjectedSalary
end
