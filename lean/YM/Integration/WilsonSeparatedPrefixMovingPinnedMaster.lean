import YM.Integration.WilsonSeparatedPrefixMovingPinFourier

/-! N-born near and exterior sources at their genuine relative positions, through the exact capture. -/
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinnedMaster
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named needed)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonIndependentMovingRosterBirthCalendar (room)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonSeparatedPrefixMovingBeforeRead (heard)
open WilsonSeparatedPrefixMovingPinSigned (slice)
open WilsonSeparatedPrefixMovingPinController (appointed)
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingPinFourier (waveRow)
open WilsonSeparatedPrefixMovingPinChamber (panel)
open MeasureTheory Finset
open scoped SchwartzMap ContDiff
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{n height seats:ℕ}

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(F:SealR G)(e h:ℕ)(positive:0<h)
    (near:∀s,Named M height seats (Q s))(far:Named M height seats F)
    (budget:needed (F.h+capP Q) 0 h ≤ seats){D:ℕ}
    (Φ:Rarity D)(ψ χ:Rarity F.D)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (windowed:∀p q:Point4,Φ.ψ.val p*ψ.ψ.val (q-p)=Φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    let u:=0
    let k:=F.h+capP Q
    let τ:=h+k
    let a:=F.h+(u+τ)
    let anew:=capP Q+F.h+(u+τ+2)
    let amid:=F.h+(u+τ+2)
    ∃first shape chron middle:Credit,∃S:𝓢(Euclid,ℂ),S=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ ∧
      (∀a:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^a)*‖S ξ‖)) ∧ ∀(R:Realm G (e+1) C)(_sold:Elected M R height seats)
      (older t b m N:ℕ)(_gate:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ b)(_formed:b ≤ m)(_top:m ≤ N)
      (φ:Wilt Q)(X:Herit Q)(Y:F.Rider)(r gap farGap DF A:ℝ)(B:Fin (n+1)→ℝ)
      (K:ℕ)(_rank:capP Q≤K)(dim:ℕ)(ye:ℝ)(o:CellR),
      let y:=paceT R.draws.S m b
      let T:=paceT R.draws.S m t
      let scale:=paceT R.draws.S m b
      let Z:=epoch R older m
      let fresh:=WilsonSeparatedPrefixMovingUnformedSector.invoice Q F X Y e k u anew r farGap DF B
      let old:=shape.buy (room r gap y)*WilsonIndependentMovingRosterInvoice.charge Q F X Y e u a r farGap DF B
      let stable:=(16*r)^u*(farGap⁻¹)^amid*coupon F Y e (u+amid) r DF*9^(u+amid)*(∏s,B s*fee (Q s) e (X s))
      let total:=2*fresh*first.buy Z+4*old*chron.buy Z+scale^h*(Z*(stable*middle.buy Z))
      Amplitude Φ A → 0<gap → 0<farGap → (∀s,Amplitude (φ s) (B s)) → Amplitude ψ DF →
      (∀s d,s≠d→ClearDay (φ s) (φ d) gap) →
      (∀s,(φ s).radius+|y|+1 ≤ r) → ψ.radius+|y/T|+1 ≤ r → 2+2*|y| ≤ r →
      room r gap y ≤ Z →
      (∀z∈tsupport ψ.ψ.val,T*farGap+max r (scale+|y|) ≤ ‖T • z‖) →
      let ε:=paceT R.draws.S t b
      let vote:=waveRow S R Q F φ Φ χ X Y t m b older N K dim ye o
      (∀q r,∀w:Fin r→YForest G,Integrable (vote q r w)∧
        panel R Q F φ ψ X Y Φ ye o t m b older N b q r w=∫ξ,vote q r w ξ)∧
      ∀w0:Fin 0→YForest G,Heard e h T ((5*radiusH Φ ε ye)^4*A*total)
        (fun q=>panel R Q F φ ψ X Y Φ ye o t m b older N N q 0 w0-∫ξ,vote q 0 w0 ξ):=by
  intro u k τ a anew amid
  obtain ⟨first,shape,chron,middle,paid⟩:=WilsonSeparatedPrefixMovingPinBefore.original M Q F e h positive near far budget
  obtain ⟨S,idS,moments,filed⟩:=WilsonSeparatedPrefixMovingPinFourier.declared (H:=H) («C»:=C) (W:=C) (V:=C) (e:=e) F Φ ψ χ hψ hχ windowed
  refine ⟨first,shape,chron,middle,S,idS,moments,?_⟩
  intro R sold older t b m N gate start home formed top φ X Y r gap farGap DF A B K rank dim ye o
    y T scale Z fresh old stable total Φincome gapPos farPos nearIncome farIncome shapes fits outerBox nearBox shield separated ε vote
  obtain ⟨owners,⟨outside⟩⟩:=WilsonIndependentMovingRosterAllFineSeats.roster sold Q F near far
  have award:=filed R outside (t:=t) (m:=m) (b:=b) (older:=older) (N:=N) Q owners φ X Y
    (gate.trans (start.trans home)) (start.trans home) (formed.trans top) (pace_le R.draws.S home) K rank dim ye o
  refine ⟨award.1,?_⟩;intro w0
  apply award.2 w0 h A total Φincome
  intro z s
  exact paid R sold older t b m N gate start home formed top φ ψ X Y z y r gap farGap DF B
    gapPos farPos nearIncome farIncome shapes fits outerBox nearBox shield separated s w0
end YM.Integration.WilsonSeparatedPrefixMovingPinnedMaster
