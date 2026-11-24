import YM.Integration.WilsonSeparatedPrefixMovingElectedPair
import YM.Integration.WilsonSeparatedPrefixMovingInvoice

/-! The two ordered joins of three genuine Mer inputs at their own reporters.
Only one fixed polynomial of the true chronological room remains. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPaidPair
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open scoped BigOperators Topology Classical

private theorem grow {D:ℕ}(φ:Rarity D)(w z v:ℝ)(hw:0≤w)(hz:w≤z):
    radiusH φ w v≤radiusH φ z v:=by unfold radiusH;rw [abs_of_nonneg hw,abs_of_nonneg (hw.trans hz)];gcongr

theorem original {G:Gauge}{H:Hol G}(Q₁ Q₂ Qe:SealR G)
    (k e u a ai target left extra deeper D:ℕ)(outerWave:a=Qe.h+extra)
    (radius:a=u+Qe.h+target+left)(innerWave:ai=Q₂.h+Q₁.h+(u+a+deeper))
    (E W V Wd Wo:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_outer:SpringD R k u a W)
      (_inner:SpringD R k (u+a) ai W)(_dorm:Dormitory R (Q₁.h+Q₂.h) (u+a) Wd)
      (_end:Dormitory R (Qe.h+(Q₁.h+Q₂.h)) u Wo)(_A:PassportC H R Q₁ W V)
      (_B:PassportC H R Q₂ W V)(_F:PassportC H R Qe W V)(older t m i j N:ℕ)
      (_gate:R.anchor ≤ older)(_read:older ≤ t)(_home:t ≤ m)(_fine:m ≤ i)(_born:i+1 ≤ j)(_top:j < N)
      (_room:Qe.h+(Q₁.h+Q₂.h) ≤ k)(φ₁:Rarity Q₁.D)(φ₂:Rarity Q₂.D)(χ:Rarity D)
      (ψ:Rarity Qe.D)(A₁:Q₁.Rider)(A₂:Q₂.Rider)(E₀:Qe.Rider)(o:CellR)
      (y nearGap farGap nearRad farRad B₁ B₂ Be:ℝ),
      let S:=R.draws.S
      let x:=paceT S m (i+1)
      let z:=paceT S m (j+1)
      let T:=paceT S m t
      let L:ℝ:=(S.block i).val
      let ℰ:=epoch R older (j+1)
      let upper₁:=locale o (Q₁.spins R.draws R.paid φ₁ m (j+1) N y A₁)
      let upper₂:=locale o (Q₂.spins R.draws R.paid φ₂ m (j+1) N y A₂)
      let outer:=locale o (Qe.spins R.draws R.paid ψ t (i+1) N (y/T) E₀)
      let pair:=cruises R.draws R.paid N (Q₁.h+Q₂.h) j (i+1)
        (JoinGap R.draws R.paid j N Q₁.h Q₂.h upper₁ upper₂)
      let receipt:=cruises R.draws R.paid N (Qe.h+(Q₁.h+Q₂.h)) i older
        (JoinGap R.draws R.paid i N Qe.h (Q₁.h+Q₂.h) outer pair)
      Amplitude φ₁ B₁ → Amplitude φ₂ B₂ → Amplitude ψ Be → 0<nearGap → 0<farGap →
      (∀p∈tsupport φ₂.ψ.val,∀q∈tsupport φ₁.ψ.val,nearGap ≤ dist p q) →
      (∀p∈tsupport χ.ψ.val,∀q∈tsupport ψ.ψ.val,T*farGap ≤ dist p (T • q)) →
      radiusH φ₁ (paceT S m j) y ≤ nearRad → radiusH φ₂ (paceT S m j) y ≤ nearRad →
      radiusH χ (x*L) y ≤ farRad → radiusH ψ (x*L/T) (y/T) ≤ farRad →
      (VisitsT φ₁ z y o).Nonempty → (VisitsT φ₂ z y o).Nonempty →
      (0:Cover)∈VisitsT χ x y o → (VisitsT ψ (x/T) (y/T) o).Nonempty →
      ∀q≤e,∀ω:Fin 0→YForest G,‖receipt.2 q 0 ω‖ ≤
        ((T^target)⁻¹*(T^left)⁻¹*x^extra*z^deeper)*C.buy ℰ*
          ((9:ℝ)^(u+a)*(16*farRad)^u*(farGap⁻¹)^a*(16*nearRad)^(u+a)*(nearGap⁻¹)^ai*
            (WilsonSeparatedPrefixMovingWages.coupon Q₁ A₁ e (u+a+ai) nearRad B₁*
             WilsonSeparatedPrefixMovingWages.coupon Q₂ A₂ e (u+a+ai) nearRad B₂*
             WilsonSeparatedPrefixMovingWages.coupon Qe E₀ e (u+a) farRad Be)):=by
  obtain ⟨carry,finish,prior⟩:=WilsonSeparatedPrefixMovingElectedPair.original (H:=H)
    Q₁ Q₂ Qe k e u a ai target left extra deeper D outerWave radius innerWave E W V Wd Wo
  refine ⟨WilsonSeparatedPrefixMovingInvoice.entry H Q₁ Q₂ Qe e k u a ai carry finish E W V,?_⟩
  intro R outerPass innerPass dorm fin home₁ home₂ farHome older t m i j N gate read home fine born top
    room φ₁ φ₂ χ ψ A₁ A₂ E₀ o y nearGap farGap nearRad farRad B₁ B₂ Be S x z T L ℰ upper₁ upper₂
    outer pair receipt at₁ at₂ atE nearPos farPos nearSep farSep cap₁ cap₂ cap center live₁ live₂ zeroSite liveF q hq ω
  have p:=prior R outerPass innerPass dorm fin home₁ home₂ farHome older t m i j N gate read home fine
    born top room φ₁ φ₂ χ ψ A₁ A₂ E₀ o y nearGap farGap nearRad farRad B₁ B₂ Be at₁ at₂ atE nearPos
    farPos nearSep farSep cap₁ cap₂ cap center live₁ live₂ zeroSite liveF q hq ω
  have tpos:0<T:=pace_pos S m t
  have xpos:0<x:=pace_pos S m (i+1)
  have zpos:0<z:=pace_pos S m (j+1)
  have orig:z≤paceT S m j:=by
    rw [←pace_step S m j]
    exact le_mul_of_one_le_right zpos.le (by exact_mod_cast (S.block j).pos)
  have big:x/T≤x*L/T:=div_le_div_of_nonneg_right
    (le_mul_of_one_le_right xpos.le (show 1≤L by change 1≤((S.block i).val:ℝ);exact_mod_cast (S.block i).pos)) tpos.le
  have sold:=WilsonSeparatedPrefixMovingInvoice.original (H:=H) (W:=W) (V:=V) R Q₁ Q₂ Qe carry finish
    k u a ai older i j gate (by omega) (by omega) A₁ A₂ E₀ φ₁ φ₂ ψ (x/T) z y (y/T) nearRad farRad
    B₁ B₂ Be nearGap farGap nearPos farPos at₁ at₂ atE ((grow φ₁ _ _ _ zpos.le orig).trans cap₁)
    ((grow φ₂ _ _ _ zpos.le orig).trans cap₂) ((grow ψ _ _ _ (div_nonneg xpos.le tpos.le) big).trans center)
  exact (p.trans (mul_le_mul_of_nonneg_left sold (by positivity))).trans_eq (mul_assoc ..).symm

end YM.Integration.WilsonSeparatedPrefixMovingPaidPair
