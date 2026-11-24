import YM.Integration.WilsonIndependentMovingRosterStableSale
import YM.Integration.WilsonIndependentMatchedRosterMoney

/-! Transport the signed first connection to the selected common home,
spending the genuine native WilsonIndependentMatchedCoverDate.age and block-length loans once. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStableRetention
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterTariff (offer factor)
open WilsonIndependentMatchedRosterPowers (profiles)
open scoped BigOperators Topology Classical
variable {n:ℕ}

theorem original (G:Gauge)(rank k e u b:ℕ)(E W V:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_later:Dormitory R rank u V)(m j N:ℕ)
      (_home:R.anchor ≤ m)(_ongoing:m ≤ j)(_date:j ≤ N)
      (d w:Fin ((n+1)+1)→ℕ)(A B:Fin ((n+1)+1)→ℝ)(Z:Era G ℝ)(T gap z budget:ℝ),
      let x:=paceT R.draws.S m (j+1)
      let r:=paceT R.draws.S m j
      let δ:=paceT R.draws.S m N
      let L:ℝ:=(ll R.draws j).L.val
      let S:=R.cash (priceWG G e k u b E W) j
      let gross:=C.buy (WilsonIndependentMatchedCoverDate.age R m j)
      1≤T → 0<gap → 0≤z → (∀s,0≤A s) → (∀s,0≤B s) →
      gross*S*L^((∑s,d s)+(∑s,w s))≤budget →
      Auth rank Z → Flush e u r Z (T^(d 0+u+u)*((n+1:ℕ)*S*pearlB u b (4*z) (gap/r)*
        nuP (coinMat k e+1) (n+1) (fun s=>offer u b (d s) (w s) z δ x (A s) (B s)))) →
      Auth rank (cruises R.draws R.paid N rank j m Z) ∧ Flush e u 1
        (cruises R.draws R.paid N rank j m Z)
        ((T^(d 0+u+u)*(budget*profiles (n+1) k e u b gap z (∏s,factor u b z*(B s*A s))))*
          r^((b:ℝ)-((∑s,d s:ℕ):ℝ))*(δ/r)^(((∑s,w s:ℕ):ℝ)/4)):=by
  obtain ⟨C,stop⟩:=waveSeen G rank e u E V
  refine ⟨C,?_⟩
  intro R later m j N home ongoing date d w A B Z T gap z budget x r δ L S gross
    zoom apt zp ap bp budgeted head paid
  have live:R.anchor ≤ j:=home.trans ongoing
  have dp:0<δ:=pace_pos ..
  have xp:0<x:=pace_pos ..
  have L₀:1≤L:=by dsimp [L];exact_mod_cast (ll R.draws j).L.pos
  have age₀:1≤WilsonIndependentMatchedCoverDate.age R m j:=by
    have height:=R.depth m home
    have ordered:=scales R.draws.S ongoing
    have count:0≤((j-m:ℕ):ℝ):=by positivity
    unfold WilsonIndependentMatchedCoverDate.age
    linarith
  have positive:0≤gross:=zero_le_one.trans (C.purchase age₀)
  have S₀:0≤S:=zero_le_one.trans ((priceWG G e k u b E W).purchase (R.depth j live))
  have wage:=WilsonIndependentMatchedRosterMoney.original (k:=k) (e:=e) (u:=u) (b:=b)
    gross S budget d w A B δ x L gap z positive S₀ ap bp xp L₀ dp apt zp budgeted
  dsimp only at wage
  have here:x*L=r:=pace_step R.draws.S m j
  rw [here] at wage
  let debt:=max 0 (R.tempC j j)
  have endBill:=stop R later m j (paceT R.draws.S m) j N N _ debt (WilsonIndependentMatchedCoverDate.age R m j)
    (pace_escort home ongoing) (PadRank.frugal R home ongoing) le_rfl date date
    (le_max_right _ _) Z Z (Fringed.same paid head (le_max_left _ _))
  have original:=pace_self R.draws.S m ▸ endBill.f_l
  have paidFinal:=mul_le_mul_of_nonneg_left wage (pow_nonneg (zero_le_one.trans zoom) (d 0+u+u))
  refine ⟨endBill.pen,?_⟩
  have changeCost:gross*(T^(d 0+u+u)*((n+1:ℕ)*S*pearlB u b (4*z) (gap/r)*
      nuP (coinMat k e+1) (n+1) (fun s=>offer u b (d s) (w s) z δ x (A s) (B s))))≤
      T^(d 0+u+u)*(budget*profiles (n+1) k e u b gap z (∏s,factor u b z*(B s*A s)))*
          r^((b:ℝ)-((∑s,d s:ℕ):ℝ))*(δ/r)^(((∑s,w s:ℕ):ℝ)/4) := by
    calc _ = T^(d 0+u+u)*(gross*((n+1:ℕ)*S*pearlB u b (4*z) (gap/r)*
          nuP (coinMat k e+1) (n+1) (fun s=>offer u b (d s) (w s) z δ x (A s) (B s)))):=by ring
         _ ≤ _:=by simpa only [mul_assoc] using paidFinal
  exact ⟨original.1.trans changeCost,fun a ha r hr=>(original.2 a ha r hr).more changeCost⟩
end YM.Integration.WilsonIndependentMovingRosterStableRetention
