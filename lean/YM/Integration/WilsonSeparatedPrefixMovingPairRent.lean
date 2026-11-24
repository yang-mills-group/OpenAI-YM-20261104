import YM.Integration.WilsonSeparatedPrefixMovingFineDeposit
import YM.Integration.WilsonSeparatedPrefixMovingOldPair

/-! The independently selected inner pair buys its later root moment at its
own first birth. The two true single-column inputs keep their filed doses. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPairRent
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{H:Hol G}{k e u a extra:ℕ}{E W V:Credit}
theorem original (R:Realm G (e+1) E)(spring:SpringD R k u a W)(Q₁ Q₂:SealR G)
    (home₁:PassportC H R Q₁ W V)(home₂:PassportC H R Q₂ W V)(m j N:ℕ)
    (beginAt:R.anchor≤m)(fine:m ≤ j)(edge:j<N)(moment:a=Q₂.h+Q₁.h+(u+extra))
    (seat:Q₁.h+Q₂.h≤k)(φ₁:Rarity Q₁.D)(φ₂:Rarity Q₂.D)(X₁:Q₁.Rider)(X₂:Q₂.Rider)
    (y gap rad Z B₁ B₂:ℝ)(o:CellR)(clock:Compar R.draws.S R.y m (j+1)≤Z)
    (positive:0<gap)(sold₁:Amplitude φ₁ B₁)(sold₂:Amplitude φ₂ B₂):
    let A:=R.draws
    let P:=ll A j
    let x:=paceT A.S m (j+1)
    let xb:=paceT A.S m j
    let X:=locale o (Q₁.spins A R.paid φ₁ m (j+1) N y X₁)
    let Y:=locale o (Q₂.spins A R.paid φ₂ m (j+1) N y X₂)
    let born:=JoinGap A R.paid j N Q₁.h Q₂.h X Y
    let salary:=R.cash (priceWG G e k u a E W) j*((16*rad)^u*((P.L.val:ℝ)/gap)^a)*
      (WilsonSeparatedPrefixMovingFineFare.unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a)
        Q₁ X₁ φ₁ Z x y B₁ * WilsonSeparatedPrefixMovingFineFare.unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a)
        Q₂ X₂ φ₂ Z x y B₂)
    (∀p∈tsupport φ₂.ψ.val,∀q∈tsupport φ₁.ψ.val,gap ≤ dist p q) →
    radiusH φ₁ xb y≤rad → radiusH φ₂ xb y≤rad →
    (VisitsT φ₁ x y o).Nonempty → (VisitsT φ₂ x y o).Nonempty →
    Auth (Q₁.h+Q₂.h) born ∧ Flush e u xb born (x^(u+extra)*salary) ∧
      Flush e u 1 born (x^extra*((P.L.val:ℝ)^u)⁻¹*salary):=by
  intro A P x xb X Y born salary apart cap1 cap2 nz1 nz2
  have step:x*P.L.val=xb:=pace_step ..
  let only:Fin (0+1)→SealR G:=fun _=>Q₂
  have degree:(∑i,(only i).h)=Q₂.h:=by simp [only]
  have table:HorizonP H R W V only:= fun _=>⟨home₂⟩
  let φ:Wilt only:=fun _=>φ₂
  let X':Herit only:=fun _=>X₂
  have paid:=WilsonSeparatedPrefixMovingFineDeposit.original (n:=0) R spring only Q₁ table home₁ j N m m
    beginAt le_rfl fine edge 0 (Q₂.h+extra) (u+extra) (by rw [degree];exact moment) (by omega)
    (by rw [degree];exact seat) φ φ₁ X' X₁ y gap rad Z (fun _=>B₂) B₁ o clock clock positive
    (fun _=>sold₂) sold₁
  dsimp only at paid
  simp only [pace_self,div_one,one_mul,one_smul,one_pow,inv_one,degree,MassP,only,pow_zero] at paid
  have got:=paid (fun _=>apart) (fun _=>step.symm ▸ cap2) (step.symm ▸ cap1) (fun _=>nz2) nz1
  have result:=got.2.2
  change Flush e u (x*P.L.val) born (R.cash (priceWG G e k u a E W) j*
    ((x^(u+extra)*((16*rad)^u*((P.L.val:ℝ)/gap)^a))*_)) at result
  rw [step] at result
  let firstFee:=WilsonSeparatedPrefixMovingFineFare.unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a)
      Q₁ X₁ φ₁ Z x y B₁
  let otherFee:=WilsonSeparatedPrefixMovingFineFare.unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a)
      Q₂ X₂ φ₂ Z x y B₂
  have collapse:(∏_i:Fin (0+1),otherFee)=otherFee:=by simp
  change Flush e u xb born (R.cash (priceWG G e k u a E W) j*
     ((x^(u+extra)*((16*rad)^u*((P.L.val:ℝ)/gap)^a))*(firstFee*∏_i:Fin (0+1),otherFee))) at result
  rw [collapse] at result
  have income:R.cash (priceWG G e k u a E W) j*
     ((x^(u+extra)*((16*rad)^u*((P.L.val:ℝ)/gap)^a))*(firstFee*otherFee))=x^(u+extra)*salary:=by
    change _=x^(u+extra)*(R.cash (priceWG G e k u a E W) j*((16*rad)^u*((P.L.val:ℝ)/gap)^a)*
      (firstFee*otherFee))
    ring
  rw [income] at result
  have second:=WilsonSeparatedPrefixMovingOldPair.promote (pace_pos A.S m j) (pace_le A.S fine) result
  refine ⟨got.2.1,result,?_⟩
  change Flush e u 1 born ((xb^u)⁻¹*(x^(u+extra)*salary)) at second
  have refund:(xb^u)⁻¹*(x^(u+extra)*salary)=x^extra*((P.L.val:ℝ)^u)⁻¹*salary:=by
    rw [←step,mul_pow,pow_add]
    have hx:x≠0:=(pace_pos A.S m (j+1)).ne'
    field_simp
  rw [refund] at second
  exact second
end YM.Integration.WilsonSeparatedPrefixMovingPairRent
