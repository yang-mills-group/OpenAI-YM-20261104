import YM.Integration.WilsonSeparatedPrefixMovingLateLaw
import YM.Integration.WilsonMovingForkSharpIncome
import YM.Integration.WilsonSeparatedPrefixMovingUnjoined

/-! The actual unjoined product on the exterior reporting date still has a
scalar. Charge its two complete columns and carry the product to the ear. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpUnjoined
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {E W K U:Credit}

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(Q:SealR G)(v:Rails h k u e)(E W K U V L:Credit):
    ∃C₀ C₁:Credit,∀(Y:CutsP H T p v E W K U),let R:=Y.vesselsC
      ∀(_ticket:PassportC H R Q W V)(_dorm:Dormitory R (k+Q.h) u L)
      (older:ℕ)(_gate:R.anchor≤older)(_room:older≤Y.m)
      (φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y Bφ Bψ:ℝ)(o:CellR),
      let Z:=epoch R older Y.ceilC
      let Z₁:=max Z (max ψ.radius |y|)
      let ratio:=paceT Y.ax.S Y.m Y.ceilC
      let nearFee:=BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^u*(Bφ*(C₀.buy Z*Y.fuel)))
      let farFee:=(hardCash e u E W V H Q).buy Z₁*(Bψ*WilsonSeparatedPrefixMovingOwnDate.fee Q e X)
      Amplitude φ Bφ → Amplitude ψ Bψ → ∀q≤e,∀ω:Fin 0→YForest G,‖(whole Y Q φ ψ X y o older 0).2 q 0 ω‖≤
        (ratio^h*WilsonMovingForkSharpIncome.gain Y)*(C₁.buy Z*(coinMat (k+Q.h) e*nearFee*farFee)):=by
  obtain ⟨C₀,C₁,paid⟩:=WilsonSeparatedPrefixMovingUnjoined.original H T p Q v E W K U V L
  refine ⟨C₀,C₁,?_⟩
  intro Y R ticket dorm older gate room φ ψ X y Bφ Bψ o Z Z₁ ratio nearFee farFee own peer q hq ω
  have window₀:=window R older Y.m Y.ceilC gate room (Nat.le_add_right _ _)
  have top:Y.m≤Y.ceilC:=Nat.le_add_right _ _
  have rank:PadRank R older Y.m Z:=
    (window R older older Y.ceilC gate le_rfl (room.trans top)).2.2.2.zone le_rfl top
  have c:Compar R.draws.S R.y Y.m Y.m≤Z₁:=by
    simpa only [Compar,Nat.sub_self,Nat.cast_zero,sub_self,add_zero] using window₀.2.1.trans (le_max_left Z (max ψ.radius |y|))
  have left:=le_trans (le_max_left ψ.radius |y|) (le_max_right Z (max ψ.radius |y|))
  have right:=le_trans (le_max_right ψ.radius |y|) (le_max_right Z (max ψ.radius |y|))
  have got:=(paid Y ticket dorm 0 (Nat.zero_le _) older (fun _=>1) Z Z₁
    (oldGuard gate room) rfl rank c φ ψ X y Bφ Bψ o left right own peer).2 q hq ω
  have incl:=WilsonMovingForkSharpIncome.initial Y C₀ Z
    (WilsonSeparatedPrefixMovingCapturedFees.age Y older gate room)
  have warm:=window₀.1
  have cc:0≤ C₁.buy Z:=zero_le_one.trans (C₁.purchase warm)
  have farWarm:1≤Z₁:=warm.trans (le_max_left ..)
  let farG:=hardCash e u E W V H Q
  have fm:0≤farG.buy Z₁:=zero_le_one.trans (farG.purchase farWarm)
  have fpos:0≤ WilsonSeparatedPrefixMovingOwnDate.fee Q e X:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have farPos:0≤farFee:=mul_nonneg fm (mul_nonneg peer.1 fpos)
  have credit:0≤coinMat (k+Q.h) e:=by unfold coinMat;positivity
  have rad:0≤radiusH φ 1 y:=by unfold radiusH;have pos:=φ.markG;positivity
  have bas:0≤BasePrice h φ 1 y:=by unfold BasePrice;positivity
  have f:=own.1
  have rat:0≤ratio:= (pace_pos ..).le
  calc
    _≤ ratio^h*(C₁.buy Z*(coinMat (k+Q.h) e*
        (BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^u*(Bφ*WilsonIndependentMatchedCoverProfile.price Y C₀ 0 1)))*farFee)):=
      by simpa only [whole,WilsonSeparatedPrefixMovingLateLaw.near,WilsonSeparatedPrefixMovingLateLaw.far,
        WilsonSeparatedPrefixMovingPairSector.current,Nat.add_zero,pace_self] using got
    _≤ ratio^h*(C₁.buy Z*(coinMat (k+Q.h) e*
        (BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^u*(Bφ*(WilsonMovingForkSharpIncome.gain Y*(C₀.buy Z*Y.fuel)))))*farFee)):=by
      gcongr
    _=_:=by dsimp only [nearFee]; ring

end YM.Integration.WilsonMovingForkSharpUnjoined
