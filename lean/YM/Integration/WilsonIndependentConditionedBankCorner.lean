import YM.Integration.WilsonIndependentConditionedBankPublicGram
import YM.Integration.WilsonIndependentConditionedPairProbeHearings

/-! The three earned stable sectors and the complete evaluated pivot table on one inherited vacuum. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankCorner
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentFittedMixedReturn (word planted)
open WilsonIndependentFittedMixedCash (bill embed)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedFittedSeat (dose receiving)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentFittedPivotCash (measured view gross)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentConditionedPairProbes (Prices Heard charge)
open WilsonIndependentConditionedBankAxes (Cuts)
open WilsonIndependentConditionedBankPublicGram (response residual)
open WilsonPositionProgramTrialHomeDose (publicDose)
variable {G:Gauge}{e k u₀:ℕ}{H:Hol G}
local notation "I" => Fin 2
local notation "L₀" => Credit.leanC
local notation "inlet" => WilsonIndependentMatchedCoverProfile.word

def fee (f:WilsonIndependentMatchedRosterMasks.Bits 1→ℝ):ℝ:=
  max (f (true,true)) (max (f (true,false)) (f (false,true)))

private theorem larger {Q:SealR G}{own:Rails Q.h k u₀ e}{E W K U:Credit}
    (X:CutsP H Q.ans Q.path own E W K U)(A B:Era G ℝ)(host u:ℕ){f s:ℝ}(up:f ≤ s)
    (h:Hearing X A B host u f):Hearing X A B host u s:=
  ⟨⟨h.1.1.trans up,fun j hj r hr=>(h.1.2 j hj r hr).more up⟩,fun j hj z=>(h.2 j hj z).trans up⟩

def input (Q:I→SealR G)(own:∀i,Rails (Q i).h k u₀ e)(E W K₀ U:Credit)
    (X:Cuts (H:=H) Q own E W K₀ U)(i:I)(a:ℝ)(φ:Rarity (Q i).D)(y:ℝ)(o:CellR):Era G ℝ:=
  inlet (a • (X i).pt) φ (paceT (X i).ax.S (X i).m (X i).ceilC) y o (Q i).h

def Bill (Q:I→SealR G)(own:∀i,Rails (Q i).h k u₀ e)(E W K₀ U:Credit)(R:Realm G (e+1) L₀)
    (X:Cuts (H:=H) Q own E W K₀ U)(host m K N q:ℕ)(g η:ℝ)(tariff₁ tariff₂:Credit)
    (a:I→ℝ)(φ:(i:I)→Rarity (Q i).D)(y:ℝ)(o:CellR)(z:Fin 0→YForest G):Prop:=
  let d:=fun i=>publicDose (Q i) (X i) (a i)
  let actual:=fun i=>input Q own E W K₀ U X i (a i) (φ i) y o
  let norm:=fun i=>amount (X i) host q g (d i)
  let high:=2*|g|^(q+1)*(reserve (X 0) host q (dose (X 0) (a 0))+
    reserve (X 1) host q (dose (X 1) (a 1)))
  ‖view (X 0) host q g (actual 0) (actual 1) z-
      response R (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 z q g (d 0) (d 1)‖ ≤
    (((q+1:ℕ):ℝ)*η)*((1+(X 0).vesselsC.cash tariff₁ (X 0).m*norm 0)*
      (1+(X 1).vesselsC.cash tariff₂ (X 1).m*norm 1)+high)+
    3*|g|^(q+1)*residual R (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 z q (d 0) (d 1)

theorem original (Q:I→SealR G)(own:∀i,Rails (Q i).h k u₀ e)(E W K₀ U Z:Credit):
    ∃L M:Credit,∀(R:Realm G (e+1) L₀)(coins:Prices)(u b:ℕ),
    Heard (H:=H) Q own E W K₀ U R coins u b →
    ∀(X:Cuts (H:=H) Q own E W K₀ U)(host m K N:ℕ),
    (∀i,Nonempty (AheadT H (X i).vesselsC W U (Q i) Z)) →
    R.anchor ≤ host → host ≤ m → m ≤ K → K ≤ N →
    (∀i,(X i).ax=R.draws) → (∀i,(X i).tx=R.paid) →
    (∀i,(X i).m=m) → (∀i,(X i).ceilC=K) → (∀i,(X i).N=N) →
    ∀(ζ:ℝ)(a:I→ℝ)(_base:(i:I)→Alma (Q i).F)(φ:(i:I)→Rarity (Q i).D)
    (y t w:ℝ)(o:CellR)(B:I→ℝ),ζ ≤ 1/4 → ((∑i,(Q i).h:ℕ):ℝ)+ζ < b →
    0<t → (∀i j,i≠j→ClearDay (φ i) (φ j) t) → (∀i,radiusH (φ i) 1 y ≤ w) →
    (∀i,Amplitude (φ i) (B i)) → ∀(q:ℕ),q ≤ e → ∀(g:ℝ),|g| ≤ 1 → ∀z,
    Bill Q own E W K₀ U R X host m K N q g
      (fee (charge Q own E W K₀ U R X coins u b host m K ζ a B t w)) L M a φ y o z:=by
  obtain ⟨L,M,priced⟩:=WilsonIndependentConditionedBankRelative.original
    (H:=H) (Q₁:=Q 0) (Q₂:=Q 1) (v₁:=own 0) (v₂:=own 1) (E:=E) (W:=W) (K:=K₀) (U:=U) Z
  refine ⟨L,M,?_⟩
  intro R coins u b enrolled X host m K N frames live older cut top files reset homes births vac
    ζ a base φ y t w o B gain room ht apart sizes bounds q order g small z
  let costs:=charge Q own E W K₀ U R X coins u b host m K ζ a B t w
  obtain ⟨both,first,second⟩:=WilsonIndependentConditionedPairProbeHearings.original Q own E W K₀ U R coins u b
    enrolled X host m K N live older cut top files reset homes births vac ζ a base φ y t w o B gain room ht apart sizes bounds
  have zero:costs (true,true)≤fee costs:=le_max_left .. 
  have one:costs (true,false)≤fee costs:=(le_max_left ..).trans (le_max_right ..)
  have two:costs (false,true)≤fee costs:=(le_max_right ..).trans (le_max_right ..)
  have low:=priced (X 0) (X 1) (frames 0).some (frames 1).some ((files 1).trans (files 0).symm)
    ((reset 1).trans (reset 0).symm) ((vac 1).trans (vac 0).symm) ((homes 1).trans (homes 0).symm)
    ((births 1).trans (births 0).symm) host ((homes 0) ▸ older) (a 0) (a 1) (φ 0) (φ 1) y o q order g small z u
    (fee costs) (both.1.1.trans zero) (larger (X 0) _ _ host u zero both)
    (fun j=>larger (X 1) _ _ host u one (first j)) (fun j=>larger (X 0) _ _ host u two (second j))
  have gram:=WilsonIndependentConditionedBankPublicGram.original R (X 0) (X 1) m K N host older
    (files 0) (reset 0) (homes 0) (births 0) (vac 0) (files 1) (reset 1) (homes 1) (births 1) (vac 1)
    (a 0) (a 1) (φ 0) (φ 1) y o 0 z q g small
  let actual:=view (X 0) host q g (input Q own E W K₀ U X 0 (a 0) (φ 0) y o)
    (input Q own E W K₀ U X 1 (a 1) (φ 1) y o) z
  let fitted:=view (X 0) host q g (receiving (X 0) (a 0) (φ 0) y o (X 0).i)
    (receiving (X 1) (a 1) (φ 1) y o (X 1).i) z
  let G:=response R (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 z q g
    (publicDose (Q 0) (X 0) (a 0)) (publicDose (Q 1) (X 1) (a 1))
  have edge:‖actual-G‖≤‖actual-fitted‖+‖fitted-G‖:=by
    simpa only [dist_eq_norm] using dist_triangle actual fitted G
  exact edge.trans (add_le_add low gram)

end YM.Integration.WilsonIndependentConditionedBankCorner
