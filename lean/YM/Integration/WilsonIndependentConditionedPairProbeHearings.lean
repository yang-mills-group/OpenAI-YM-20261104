import YM.Integration.WilsonIndependentConditionedPairProbes
import YM.Integration.WilsonIndependentMatchedPivotStop

/-! The three literal hearings consumed by the heterogeneous bilinear comparison. The probe entry may vary over the entire opposite pivot basis after the prices are settled. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPairProbeHearings
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterMasks (Bits quiet)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentConditionedBankAxes (Cuts)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentConditionedPairProbes (Prices Heard charge reading names)
open WilsonIndependentMatchedPivotStop (Hearing)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e k u₀:ℕ}{H:Hol G}
local notation "J" => Fin 2
local notation "L₀" => Credit.leanC

theorem original (Q:J→SealR G)(own:∀i,Rails (Q i).h k u₀ e)(E W K₀ U:Credit)
    (R:Realm G (e+1) L₀)(coins:Prices)(u b:ℕ)(supply:Heard (H:=H) Q own E W K₀ U R coins u b)
    (X:Cuts (H:=H) Q own E W K₀ U)(host m K N:ℕ)
    (live:R.anchor ≤ host)(older:host ≤ m)(cut:m ≤ K)(vac:K ≤ N)
    (files:∀i,(X i).ax=R.draws)(reset:∀i,(X i).tx=R.paid)
    (homes:∀i,(X i).m=m)(birth:∀i,(X i).ceilC=K)(top:∀i,(X i).N=N)
    (ζ:ℝ)(a:J→ℝ)(base:(i:J)→Alma (Q i).F)(φ:(i:J)→Rarity (Q i).D)
    (y t z:ℝ)(o:CellR)(B:J→ℝ)(gain:ζ ≤ 1/4)(room:((∑i,(Q i).h:ℕ):ℝ)+ζ < b)
    (ht:0<t)(clear:∀i j,i≠j→ClearDay (φ i) (φ j) t)
    (sizes:∀i,radiusH (φ i) 1 y ≤ z)(bounds:∀i,Amplitude (φ i) (B i)):
    let Δ:=fun s:J=>seat (X s) (a s) (φ s) y o (X s).i
    let P:=fun (s:J)(j:Alma (Q s).F)=>film (X s) j 0 (φ s) y o (X s).i
    let fee:=charge Q own E W K₀ U R X coins u b host m K ζ a B t z
    Hearing (X 0) (Δ 0) (Δ 1) host u (fee (true,true)) ∧
      (∀j,Hearing (X 1) (Δ 0) (P 1 j) host u (fee (true,false))) ∧
      (∀j,Hearing (X 0) (P 0 j) (Δ 1) host u (fee (false,true))):=by
  classical
  intro Δ P fee
  have earned (j:(s:J)→Alma (Q s).F)(mask:Bits 1)(hm:mask≠quiet 1):=
    supply X host m K N live older cut vac files reset homes birth top ζ a j φ y t z o B
      gain room ht clear sizes bounds mask hm
  have transfer (s:J)(P Q:Era G ℝ)(f:ℝ)
      (read:response e u (cruises R.draws R.paid N (2*k) K host (agateV P Q)) f):
      Hearing (X s) P Q host u f:=by
    change response e u (cruises (X s).ax (X s).tx (X s).N (k+k) (X s).ceilC host (agateV P Q)) f
    rw [files s,reset s,top s,birth s,← two_mul k]
    exact read
  refine ⟨?_,?_,?_⟩
  · have hit:=earned base (true,true) (by intro h; exact Bool.noConfusion (show true=false from congrArg Prod.fst h))
    rw [(names Q own E W K₀ U R X host K N a base φ y o).2.2] at hit
    exact transfer 0 _ _ _ hit
  · intro j
    let chosen:=Function.update base 1 j
    have hit:=earned chosen (true,false) (by intro h; exact Bool.noConfusion (show true=false from congrArg Prod.fst h))
    rw [(names Q own E W K₀ U R X host K N a chosen φ y o).1] at hit
    simpa only [chosen,Function.update_self] using transfer 1 _ _ _ hit
  · intro j
    let chosen:=Function.update base 0 j
    have hit:=earned chosen (false,true) (by intro h; exact Bool.noConfusion (show true=false from congrArg Prod.snd h))
    rw [(names Q own E W K₀ U R X host K N a chosen φ y o).2.1] at hit
    simpa only [chosen,Function.update_self] using transfer 0 _ _ _ hit

end YM.Integration.WilsonIndependentConditionedPairProbeHearings
