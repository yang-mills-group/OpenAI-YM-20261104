import YM.Integration.WilsonThermometerUnitFilingWeakStrip
import YM.Integration.WilsonThermometerUnitFilingWeakRibbon

/-! The neutral marked rows contract on the selected original physical calendar, including the coarse root displacement. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakStep
open Finset Lattice Laurent Bloch Metric Exterior Precision RG Next.Free Work.F08
open AllOrder AllOrder.Floe Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FormalBulk08 Flat WilsonThermometerUnitFilingWeakRoom WilsonThermometerUnitFilingWeakKernel
open scoped BigOperators Classical
variable {G:Gauge}{I J:Type*} [Fintype J]

theorem met (G:Gauge)(K:KernelChoices)(x j t:ℕ)(hj:j≤x+1)(ht:t≤x+1)
    {L:Side}(bought:floor G K x≤L.val)(A:Bloch.Row I J)(col:(Fintype.card J:ℝ)≤groups)
    {s:ℝ}(cap:s≤1)(d:ℕ):Real.exp (8*s)*cash A ((book G K j t).cost/(L.val:ℝ)^(1+d))≤1:=by
  have cost:=(issued G K x j t hj ht).2
  have positive:= (book G K j t).cost_pos
  have high:0≤ceiling G K x:=positive.le.trans cost
  have geo:Real.exp (8*s)≤Real.exp 8:=Real.exp_le_exp.mpr (by linarith)
  have origin:Real.exp 8*groups*ceiling G K x≤(L.val:ℝ):=
    (Nat.le_ceil _).trans (by exact_mod_cast bought)
  have h:Real.exp (8*s)*(Fintype.card J:ℝ)*(book G K j t).cost≤(L.val:ℝ):=
    (mul_le_mul (mul_le_mul geo col (by positivity) (Real.exp_pos _).le) cost positive.le
      (mul_nonneg (Real.exp_pos _).le ((Nat.cast_nonneg _).trans col))).trans origin
  calc _=Real.exp (8*s)*(Fintype.card J:ℝ)*(book G K j t).cost/(L.val:ℝ)^(1+d):=by unfold cash;ring
       _≤1:=gain h d

theorem bought (Q:WilsonOriginalCompoundStrip.Request G)(R:Run G)
    (p:WilsonOriginalProfileStrip.Filed (WilsonOriginalCompoundStrip.programme
       (WilsonThermometerUnitFilingWeakStrip.enrolled Q)) R.kit)(i H:ℕ)(fit:H≤R.alloy.B.a.clock.J i)
    {j t:ℕ}(hj:4≤j)(ht:4≤t)(hi:j≤R.alloy.B.a.clock.J i+1)(ti:t≤R.alloy.B.a.clock.J i+1)
    (P:Flight j t)(course:(R.alloy.B.a.clock.factor (R.alloy.B.a.clock.J i)).val≤P.L.val)
    (l:List Axis)(live:l.length≤j-2):
    let K:=R.metals.p.kernel
    let s:=WilsonThermometerUnitFilingWeakStrip.trial Q K (R.alloy.B.a.clock.J i) H
    let w:=WilsonThermometerUnitFilingWeakStrip.trial Q K j H
    let A:=advanceC P.L (P.duo K.penalty).A0 l
    let C:=advanceC P.L (P.psi K.penalty) l
    ∀ (r:ℕ) (x:Cover) (z:Fin r → Cover),
      (∀ (key:Fin r → _) (box:Fin r → Finset Cover),WilsonThermometerUnitFilingWeakRibbon.after P.L s A x z key box≤
          WilsonThermometerUnitFilingWeakRibbon.old w r x z) ∧
      (∀ (key:Fin r → _) (box:Fin r → Finset Cover),WilsonThermometerUnitFilingWeakRibbon.after P.L s C x z key box≤
          WilsonThermometerUnitFilingWeakRibbon.old w r x z):=by
  let K:=R.metals.p.kernel
  let n:=R.alloy.B.a.clock.J i
  let s:=WilsonThermometerUnitFilingWeakStrip.trial Q K n H
  let w:=WilsonThermometerUnitFilingWeakStrip.trial Q K j H
  let receipt:=book G K j t
  have staff:=receipt.serves hj ht
  obtain ⟨-,floor₀,sp,cap,aperture,-,cross⟩:=WilsonThermometerUnitFilingWeakStrip.date Q R p i H fit
  have bp:floor G K n≤P.L.val:=floor₀.trans course
  have hs:s≤receipt.width:=aperture.trans (issued G K n j t hi ti).1
  have shrink:s/(P.L.val:ℝ)≤w:=
    (div_le_div_of_nonneg_left sp.le (by exact_mod_cast (R.alloy.B.a.clock.factor n).pos)
      (by exact_mod_cast course)).trans (cross j H hi (fit.trans (Nat.le_succ _)))
  have A:=strip_mono (staff.linear P l live).1 hs le_rfl
  have C:=strip_mono (staff.curvature P l live) hs le_rfl
  dsimp only
  intro r x z
  refine ⟨fun key box=>WilsonThermometerUnitFilingWeakRibbon.original P.L sp.le shrink _ A ?_ x z key box,
    fun key box=>WilsonThermometerUnitFilingWeakRibbon.original P.L sp.le shrink _ C ?_ x z key box⟩
  · exact met G K n j t hi ti bp _ (le_max_left ..) cap l.length
  · have pay:=met G K n j t hi ti bp (advanceC P.L (P.psi K.penalty) l) (le_max_right ..) cap (1+l.length)
    simpa only [←Nat.add_assoc] using pay


theorem original (Q:WilsonOriginalCompoundStrip.Request G)(R:Run G)
    (p:WilsonOriginalProfileStrip.Filed (WilsonOriginalCompoundStrip.programme
       (WilsonThermometerUnitFilingWeakStrip.enrolled Q)) R.kit)(i H:ℕ)(fit:H≤R.alloy.B.a.clock.J i)
    {j t:ℕ}(hj:4≤j)(ht:4≤t)(hi:j≤R.alloy.B.a.clock.J i+1)(ti:t≤R.alloy.B.a.clock.J i+1)
    (P:Flight j t)(course:P.L=R.alloy.B.a.clock.factor (R.alloy.B.a.clock.J i))
    (l:List Axis)(live:l.length≤j-2):
    let K:=R.metals.p.kernel
    let s:=WilsonThermometerUnitFilingWeakStrip.trial Q K (R.alloy.B.a.clock.J i) H
    let w:=WilsonThermometerUnitFilingWeakStrip.trial Q K j H
    let A:=advanceC P.L (P.duo K.penalty).A0 l
    let C:=advanceC P.L (P.psi K.penalty) l
    ∀ (r:ℕ) (x:Cover) (z:Fin r → Cover),
      (∀ (key:Fin r → _) (box:Fin r → Finset Cover),WilsonThermometerUnitFilingWeakRibbon.after P.L s A x z key box≤
          WilsonThermometerUnitFilingWeakRibbon.old w r x z) ∧
      (∀ (key:Fin r → _) (box:Fin r → Finset Cover),WilsonThermometerUnitFilingWeakRibbon.after P.L s C x z key box≤
          WilsonThermometerUnitFilingWeakRibbon.old w r x z) :=by
  exact bought Q R p i H fit hj ht hi ti P (by rw [course]) l live

 
theorem block (R:Run G)(N i:ℕ):
    (R.alloy.B.a.clock.factor (R.alloy.B.a.clock.J i)).val≤(destination R.alloy.B.a N i).L.val:=by
  change _≤(R.alloy.B.a.S.block i).val
  rw [←R.alloy.B.a.fits.sameFactor i]
  exact R.alloy.B.a.fits.monotoneL (R.alloy.B.a.fits.mono (Nat.le_succ _))

