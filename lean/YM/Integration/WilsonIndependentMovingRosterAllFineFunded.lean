import YM.Integration.WilsonIndependentMovingRosterAllFineSeats

/-! The signed fine-cut comparison on the appointed canonical ports. Its
additional spatial power pays the native output-rank condition. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterAllFineFunded
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named needed)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonIndependentMovingRosterCut (residual)
open WilsonIndependentMovingRosterBirthCalendar (room)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open Finset
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{e n height seats:ℕ}

theorem cheaper {t τ:ℕ}{T p:ℝ}{f:ℕ→ℝ}(home:1 ≤ T)(power:t ≤ τ)(paid:Heard e τ T p f):Heard e t T p f:=by
  have pos:0<T:=lt_of_lt_of_le zero_lt_one home
  have issued:0 ≤ p:=nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (paid.1 0 (Nat.zero_le _)))
    (inv_pos.mpr (pow_pos pos _))
  have fee:(T^τ)⁻¹*p ≤ (T^t)⁻¹*p:=mul_le_mul_of_nonneg_right
    (inv_anti₀ (pow_pos pos t) (pow_le_pow_right₀ home power)) issued
  refine ⟨fun q hq=>(paid.1 q hq).trans fee,fun g g0 g1=>?_⟩
  obtain ⟨full,tail⟩:=paid.2 g g0 g1
  refine ⟨full.trans (mul_le_mul_of_nonneg_left fee (sum_nonneg fun q _=>pow_nonneg g0 q)),fun J=>?_⟩
  exact (tail J).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left fee (pow_nonneg g0 _)) (by positivity))

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(F:SealR G)(e u target:ℕ)(positive:0<target)
    (near:∀s,Named M height seats (Q s))(far:Named M height seats F)
    (budget:needed (F.h+capP Q) u target ≤ seats):
    let k:=F.h+capP Q
    let τ:=target+k
    let a:=F.h+(u+τ)
    let b:=capP Q+F.h+(u+τ+2)
    ∃first shape chron:Credit,∀(R:Realm G (e+1) C)(_sold:Elected M R height seats)
      (older t m N:ℕ)(_gate:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ m)(_top:m ≤ N)
      (φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)(y r inner outer DF:ℝ)(B:Fin (n+1)→ℝ),
      let T:=paceT R.draws.S m t
      let Z:=epoch R older m
      let fresh:=WilsonSeparatedPrefixMovingUnformedSector.invoice Q F X Y e k u b r outer DF B
      let formed:=shape.buy (room r inner y)*WilsonIndependentMovingRosterInvoice.charge Q F X Y e u a r outer DF B
      let price:=2*fresh*first.buy Z+4*formed*chron.buy Z
      0 < inner → 0 < outer → (∀s,Amplitude (φ s) (B s)) → Amplitude ψ DF →
      (∀s b,s≠b→ClearDay (φ s) (φ b) inner) →
      (∀s,∀p∈tsupport (φ s).ψ.val,∀z∈tsupport ψ.ψ.val,T*outer ≤ dist p (T • z)) →
      (∀z∈tsupport ψ.ψ.val,T*outer+1+|y| ≤ ‖T • z‖) →
      (∀s,(φ s).radius+|y|+1 ≤ r) → ψ.radius+|y/T|+1 ≤ r → 2+2*|y| ≤ r →
      ∀ω:Fin 0→YForest G,Heard e target T price (fun q=>(residual R Q F φ ψ X Y o y t m older N).2 q 0 ω):=by
  intro k τ a b
  have active:0<τ:=by dsimp only [τ];omega
  obtain ⟨first,shape,chron,issued⟩:=WilsonIndependentMovingRosterAllFine.original H Q F k e u τ active C C C C C C
  refine ⟨first,shape,chron,?_⟩
  intro R sold older t m N gate start home top φ ψ X Y o y r inner outer DF B T Z fresh formed price
    ip op amps amp apart sep remote nbox fbox cbox ω
  obtain ⟨freshSpring,outerSpring,innerSpring,dorm,terminal,_⟩:=WilsonIndependentMovingRosterAllFineSeats.finance sold Q F u target budget
  obtain ⟨roster,⟨exterior⟩⟩:=WilsonIndependentMovingRosterAllFineSeats.roster sold Q F near far
  exact cheaper (pace_ge R.draws.S home) (Nat.le_add_right _ _) (issued R freshSpring outerSpring innerSpring
    dorm terminal roster exterior older t m N gate start home top le_rfl φ ψ X Y o y r inner outer DF B ip op amps amp
    apart sep remote nbox fbox cbox ω)

end YM.Integration.WilsonIndependentMovingRosterAllFineFunded
