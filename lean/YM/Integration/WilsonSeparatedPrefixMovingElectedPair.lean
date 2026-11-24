import YM.Integration.WilsonSeparatedPrefixMovingPairRent
import YM.Integration.WilsonSeparatedPrefixMovingSecondBirth
import YM.Integration.WilsonSeparatedPrefixMovingWages

/-! A complete same-top, two-birth Mer term from the three appointed
finite-column data to its chosen older rank-zero physical test. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingElectedPair
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open scoped BigOperators Topology Classical

private theorem payment (f c h b T L x z v w M:ℝ)(p d:ℕ)(ne:z≠0):
    f*(b*((T*L*x*v)*(w*((9:ℝ)^p*(c*(((z*M)^p)⁻¹*(z^(p+d)*h)))))))=
      T*L*x*z^d*(f*c*9^p*(M^p)⁻¹*(b*v*w)*h):=by
  rw [mul_pow, _root_.mul_inv_rev, pow_add]
  have unit:(z^p)⁻¹*z^p=1:=inv_mul_cancel₀ (pow_ne_zero p ne)
  calc
    _=((z^p)⁻¹*z^p)*(T*L*x*z^d*(f*c*9^p*(M^p)⁻¹*(b*v*w)*h)):=by ring
    _=_:=by rw [unit,one_mul]

theorem original {G:Gauge}{H:Hol G}(Q₁ Q₂ Qe:SealR G)
    (k e u a ai target left extra deeper D:ℕ)(outerWave:a=Qe.h+extra)
    (radius:a=u+Qe.h+target+left)(innerWave:ai=Q₂.h+Q₁.h+(u+a+deeper))
    (E W V Wd Wo:Credit):
    ∃carry finish:Credit,∀(R:Realm G (e+1) E)(_outer:SpringD R k u a W)
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
      let M:ℝ:=(S.block j).val
      let ℰ:=epoch R older (j+1)
      let upper₁:=locale o (Q₁.spins R.draws R.paid φ₁ m (j+1) N y A₁)
      let upper₂:=locale o (Q₂.spins R.draws R.paid φ₂ m (j+1) N y A₂)
      let outer:=locale o (Qe.spins R.draws R.paid ψ t (i+1) N (y/T) E₀)
      let pair:=cruises R.draws R.paid N (Q₁.h+Q₂.h) j (i+1)
        (JoinGap R.draws R.paid j N Q₁.h Q₂.h upper₁ upper₂)
      let receipt:=cruises R.draws R.paid N (Qe.h+(Q₁.h+Q₂.h)) i older
        (JoinGap R.draws R.paid i N Qe.h (Q₁.h+Q₂.h) outer pair)
      let innerFee:=R.cash (priceWG G e k (u+a) ai E W) j*((16*nearRad)^(u+a)*(M/nearGap)^ai)*
        (unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a+ai) Q₁ A₁ φ₁ ℰ z y B₁*
         unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a+ai) Q₂ A₂ φ₂ ℰ z y B₂)
      let outerFee:=R.cash (priceWG G e k u a E W) i*((16*farRad)^u*(L/farGap)^a)*
        unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a) Qe E₀ ψ ℰ (x/T) (y/T) Be
      Amplitude φ₁ B₁ → Amplitude φ₂ B₂ → Amplitude ψ Be → 0<nearGap → 0<farGap →
      (∀p∈tsupport φ₂.ψ.val,∀q∈tsupport φ₁.ψ.val,nearGap ≤ dist p q) →
      (∀p∈tsupport χ.ψ.val,∀q∈tsupport ψ.ψ.val,T*farGap ≤ dist p (T • q)) →
      radiusH φ₁ (paceT S m j) y ≤ nearRad → radiusH φ₂ (paceT S m j) y ≤ nearRad →
      radiusH χ (x*L) y ≤ farRad → radiusH ψ (x*L/T) (y/T) ≤ farRad →
      (VisitsT φ₁ z y o).Nonempty → (VisitsT φ₂ z y o).Nonempty →
      (0:Cover)∈VisitsT χ x y o → (VisitsT ψ (x/T) (y/T) o).Nonempty →
      ∀q≤e,∀ω:Fin 0→YForest G,‖receipt.2 q 0 ω‖ ≤
        ((T^target)⁻¹*(T^left)⁻¹*x^extra*z^deeper)*
          (finish.buy (epoch R older i)*carry.buy ℰ*(9:ℝ)^(u+a)*(M^(u+a))⁻¹*outerFee*innerFee):=by
  obtain ⟨carry,next⟩:=WilsonSeparatedPrefixMovingSecondBirth.original Qe Q₁.h Q₂.h k e u a target
    left extra D outerWave radius E W V Wd
  obtain ⟨finish,arrive⟩:=WilsonSeparatedPrefixMovingWages.earlier G (Qe.h+(Q₁.h+Q₂.h)) e u E Wo
  refine ⟨carry,finish,?_⟩
  intro R outerPass innerPass dorm fin home₁ home₂ farHome older t m i j N gate read home fine born top
    room φ₁ φ₂ χ ψ A₁ A₂ E₀ o y nearGap farGap nearRad farRad B₁ B₂ Be S x z T L M ℰ upper₁ upper₂
    outer pair receipt innerFee outerFee at₁ at₂ atE nearPos farPos nearSep farSep cap₁ cap₂ cap center
    live₁ live₂ zeroSite liveF q hq ω
  have background:=gate.trans (read.trans home)
  have wn:=window R older m (j+1) gate (read.trans home) (by omega)
  have p:=WilsonSeparatedPrefixMovingPairRent.original R innerPass Q₁ Q₂ home₁ home₂ m j N background (by omega)
    top innerWave (by omega) φ₁ φ₂ A₁ A₂ y nearGap nearRad ℰ B₁ B₂ o wn.2.2.1 nearPos at₁ at₂
    nearSep cap₁ cap₂ live₁ live₂
  have atBirth:Flush e (u+a) (paceT S m j) (JoinGap R.draws R.paid j N Q₁.h Q₂.h upper₁ upper₂)
      (z^(u+a+deeper)*innerFee):=p.2.1
  have qa:Auth Q₁.h upper₁:=(WilsonSeparatedPrefixMovingOwnDate.column home₁ m (j+1) N (u+a+ai)
    background (by omega) top ℰ wn.2.2.1 A₁ φ₁ y o (ll R.draws j) B₁ at₁).1
  have qb:Auth Q₂.h upper₂:=(WilsonSeparatedPrefixMovingOwnDate.column home₂ m (j+1) N (u+a+ai)
    background (by omega) top ℰ wn.2.2.1 A₂ φ₂ y o (ll R.draws j) B₂ at₂).1
  have all:=window R older older (j+1) gate le_rfl (by omega)
  have windowT:Compar S R.y t (i+1) ≤ ℰ:=by
    have bound:epoch R older (i+1)≤ℰ:=by
      dsimp only [WilsonSeparatedPrefixMovingCalendar.epoch,ℰ];linarith only [scales R.draws.S (show i+1≤j+1 by omega)]
    exact (window R older t (i+1) gate read (by omega)).2.2.1.trans bound
  have sold:=next R outerPass dorm farHome t m i j N (gate.trans read) home fine born top room
    upper₁ upper₂ qa qb χ ψ E₀ y farGap farRad ℰ ℰ (z^(u+a+deeper)*innerFee) Be o atBirth
    (all.2.2.2.zone (by omega) (by omega)) windowT atE farPos zeroSite farSep cap center liveF
  have edge:=sold.2.2
  let second:=JoinGap R.draws R.paid i N Qe.h (Q₁.h+Q₂.h) outer pair
  have earned:=arrive R fin older m i N gate (read.trans home) fine (by omega) second sold.2.1 _
    (by rw [←pace_step S m i];exact edge) q hq ω
  have trueGauge:paceT S m j=z*M:= (pace_step S m j).symm
  let bump:=R.cash (priceWG G e k u a E W) i
  let bezel:=(16*farRad)^u*(L/farGap)^a
  let ωe:=unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a) Qe E₀ ψ ℰ (x/T) (y/T) Be
  change ‖receipt.2 q 0 ω‖≤finish.buy (epoch R older i)*(bump*((((T^target)⁻¹*(T^left)⁻¹*
    x^extra*bezel))*(ωe*(9^(u+a)*(carry.buy ℰ*(((paceT S m j)^(u+a))⁻¹*(z^(u+a+deeper)*innerFee))))))) at earned
  change ‖receipt.2 q 0 ω‖≤_*(_*_*_*_*(bump*bezel*ωe)*innerFee)
  refine earned.trans_eq ?_
  rw [trueGauge]
  exact payment _ _ _ _ _ _ _ z _ _ M (u+a) deeper (pace_pos S m (j+1)).ne'

end YM.Integration.WilsonSeparatedPrefixMovingElectedPair
