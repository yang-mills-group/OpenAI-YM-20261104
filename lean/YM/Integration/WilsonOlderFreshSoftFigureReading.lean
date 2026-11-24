import YM.Integration.WilsonOlderFreshSoftFigures
import YM.Integration.WilsonOlderFreshSoftOrdinary
import YM.Integration.WilsonOriginalPublicFigureIncome

/-! Scalar readings of the complete fitted ordinary word on one fixed-child chronology. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftFigureReading
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Soil
open WilsonCoeffUV.Cosmos PhysicalNext.Repeat.Legato OriginalMarkedSourceComet
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshHybridClock (flat)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftFigures (stencil)
open WilsonOlderFreshSoftOrdinary (material)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[Fintype ι][LinearOrder ι]
variable (R:Run G)(D d:ι→ℕ)
local notation "F" i:max=>R.family.labels.level (d i)

def upper (κ:(j:ι)→Knob (D j))(pt:ι→Chamber)(b:∀i,(F i).Index)(L:Levels G)(O:ChartRatio G)
    (N:ℕ)(cells:Digits L ι)(c K:ℕ)(y:ι → Cover)(T:Finset ι)(f:Pen D T→L[ℝ] ℝ):Era G ℝ:=
  material D d L O (stencil R D d b κ pt) N cells c K y T f

def reading (g:ℝ)(x:∀i,(F i).Coeff)(P:(∀i,(F i).Index)→Era G ℝ)(q:ℕ)(t:ℝ):ℂ:=
  ∑b,WilsonOriginalPublicTrialFigure.weight R d g x b*(flat (P b) q t:ℂ)

private theorem sumBound {α:Type}[Fintype α](w:α→ℂ)(x y:α→ℝ)(C:ℝ)
    (fee:∀b,‖x b-y b‖≤C):
    ‖(∑b,w b*(x b:ℂ))-(∑b,w b*(y b:ℂ))‖≤(∑b,‖w b‖)*C:=by
  rw [←sum_sub_distrib,sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro b _
  rw [←mul_sub,←Complex.ofReal_sub,norm_mul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (fee b) (norm_nonneg _)

theorem original (e:ℕ):
    ∃B:ℝ,1≤B ∧ ∀(T:Finset ι),T.Nonempty → ∃U V:Credit,
      ∀(S:Realm G (e+1) Credit.leanC),Dormitory S (mass d T) 0 Credit.leanC →
      ∀(N K c w v:ℕ),S.anchor≤v → v≤w → w≤c → c≤K → K≤N →
      ∀(Z₀ Z:ℝ),PadRank S c K Z₀ → PadRank S v w Z →
      ∀(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)(cells:Digits S.draws ι)
        (y:ι → Cover)(f:Pen D T→L[ℝ] ℝ),‖f‖≤1 →
      let P:=fun b=>upper R D d κ pt b S.draws S.paid N cells c K y T f
      let h:=mass d T
      let H:=fun b=>cruises S.draws S.paid N h c w (P b)
      let full:=fun b=>cruises S.draws S.paid N h c v (P b)
      let retained:=fun b=>cruises S.draws S.paid N h w v (scalarOnly (H b))
      let initial:=(WilsonIndependentCollarOrdinaryWeak.price G h e).buy Z₀*B^T.card
      let fare:=S.cash U w*S.tempC w c*initial
      (∀b,Auth h (P b) ∧ Saturation e 0 0 (P b).2 1 initial ∧
        Saturation e 1 0 (H b).2 1 fare ∧ Saturation e 0 0 (full b-retained b).2 1 (V.buy Z*fare)) ∧
      ∀q≤e,∀(t g:ℝ)(x:∀i,(F i).Coeff),
      ‖reading R d g x full q t-reading R d g x retained q t‖≤
        (∑b,‖WilsonOriginalPublicTrialFigure.weight R d g x b‖)*((∑j∈range (q+1),|t|^j)*(V.buy Z*fare)):=by
  obtain ⟨C,cp,stock⟩:=WilsonOlderFreshSoftFigures.original R D d e (w:=1) zero_lt_one
  obtain ⟨A,ap,price⟩:=WilsonOlderFreshSoftOrdinary.original G D d e
  refine ⟨A*C,one_le_mul_of_one_le_of_one_le ap cp,?_⟩
  intro T hs
  obtain ⟨U,V,heard⟩:=price T hs
  refine ⟨U,V,?_⟩
  intro S dorm N K c w v first vw wc cK KN Z₀ Z early late κ pt cells y f fn P h H full retained initial fare
  let receipt (b:∀i,(F i).Index):=
    heard S dorm N K c w v first vw wc cK KN Z₀ Z early late
      (stencil R D d b κ pt) (stock b κ pt).1 C (zero_le_one.trans cp) (stock b κ pt).2 cells y f fn
  refine ⟨fun b=>⟨(receipt b).1,(receipt b).2.1,(receipt b).2.2.1,(receipt b).2.2.2.1⟩,?_⟩
  intro q hq t g x
  apply sumBound
  exact fun b=>(receipt b).2.2.2.2 q hq t

end YM.Integration.WilsonOlderFreshSoftFigureReading
end
