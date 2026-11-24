import YM.Integration.WilsonIndependentMatchedOwnHomeKShell

/-! On the shared normalized prior, the complete upper measurement first loses its
exterior-crossing rows, then its earlier jointly deposited near fields. All
three entries below are actual integrated group measurements at the same sites. -/
noncomputable section
set_option warningAsError true
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedPrefixMovingOrdinarySwitch
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMovingRosterAllFineSeats (Named Elected needed)
open WilsonSeparatedPrefixMovingPinnedRaw (raw)
open WilsonSeparatedPrefixMovingPinnedPupil (Clear)
open WilsonIndependentMovingRosterBirthCalendar (room)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonIndependentSpoutMasterCoordinates (axis)

open scoped BigOperators Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{n e d height seats:ℕ}


open WilsonIndependentMatchedOwnHomePanel (born)
open WilsonSeparatedPrefixMovingPinChamber (panel)
open WilsonIndependentMatchedOwnHomeKShell (Coins cost)

inductive Birth | upper | held | planted

def tape (u:Birth)(R:Realm G (e+1) C)(Q:Fin (n+1)→SealR G)(F:SealR G)(α:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(Φ:Rarity d)(y:ℝ)(o:CellR)(t m b older K N:ℕ)(ρ:ℝ)(ω:Fin 0→YForest G):Cost:=
  PowerSeries.mk fun j=>ρ^4*(paceT R.draws.S m t^F.h)⁻¹*match u with
    | .upper=>raw R Q F α ψ X Y Φ y o t m b older N j 0 ω
    | .held=>panel R Q F α ψ X Y Φ y o t m b older N K j 0 ω
    | .planted=>born R Q F α ψ X Y Φ y o t m b older K N j 0 ω

private theorem add_price {a b c x z P Q:ℝ}(pos:0≤x)(first:‖a-b‖≤P)(second:‖x*(b-c)‖≤Q):
    ‖z*x*a-z*x*c‖ ≤ |z| *(x*P+Q):=by
  rw [show z*x*a-z*x*c=z*(x*(a-b)+x*(b-c)) by ring,norm_mul,Real.norm_eq_abs z]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add ?_ second)
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg pos];gcongr

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(F:SealR G)(e p ex:ℕ)(positive:0<p)
    (gain:2 ≤ F.h+ex)(near:∀s,Named M height seats (Q s))(far:Named M height seats F)
    (capacity:needed (F.h+capP Q) 0 p ≤ seats)(reserve:capP Q+F.h+ex ≤ seats)(W:Credit):
    ∃book:Coins,∀(R:Realm G (e+1) C)(_stock:Elected M R height seats)(_forward:AheadT H R C C F W)
    (older t b m K N:ℕ),R.anchor ≤ older → older ≤ t → t ≤ b → b ≤ m → m ≤ K → K ≤ N →
    ∀(α:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(a:Alma F.F)(r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ)
      (Φ:Rarity d)(y amp:ℝ)(o:CellR) (w:Fin 0→YForest G),
    Clear R Q F α ψ older t b m r gap farGap DF B → Amplitude Φ amp →
    ∀ρ:ℝ,let Y:=PermuteLens R.draws R.paid F N t (brought R.draws R.paid F N t m (axis F a))
    let read:=fun u=>tape u R Q F α ψ X Y Φ y o t m b older K N ρ w
    read .upper-read .planted=(read .upper-read .held)+(read .held-read .planted) ∧
    ∀j≤e, ‖PowerSeries.coeff j (read .upper-read .planted)‖ ≤ cost book H R Q F X a ψ Φ y amp older t b m K N p ex r gap farGap DF B ρ 0:=by
  obtain ⟨first,shape,chron,suffix⟩:=WilsonIndependentMatchedOwnHomeFundedPrefix.original (d:=d) M Q F e p positive near far capacity
  obtain ⟨forward,inverse,terminal,regional,reach,interior⟩:=
    WilsonIndependentMatchedOwnHomeInteriorSale.original (d:=d) H Q F e ex gain C C C W C C C
  let book:Coins:=⟨Credit.unit,first,shape,chron,forward,inverse,terminal,regional,reach⟩
  refine ⟨book,?_⟩
  intro R stock direction older t b m K N awake start atFar middle cut top α ψ X a r gap farGap DF B Φ y amp o w geometry volume ρ Y read
  refine ⟨by abel,?_⟩
  have past:=suffix R stock older t b m K N awake start atFar middle cut top α ψ X Y r gap farGap DF B Φ y amp o w geometry volume
  obtain ⟨roster,_⟩:=WilsonIndependentMovingRosterAllFineSeats.roster stock Q F near far
  have native:=interior R roster direction (stock.spring _ _ _ (by omega) (by omega) (by omega))
    (stock.dorm _ _ (by omega) (by omega)) (stock.dorm _ _ (by omega) (by omega))
    older t b m K N awake start atFar middle cut top α ψ X a Φ amp DF y (room r gap (paceT R.draws.S m b)) B o volume geometry.2.2.2.1
  have cover:=WilsonIndependentMovingRosterBirthCalendar.geometry Q α B r gap (paceT R.draws.S m b) geometry.1 geometry.2.2.1
    (fun s=>by have hh:=geometry.2.2.2.2.2.1 s;have nn:=abs_nonneg (paceT R.draws.S m b);linarith) geometry.2.2.2.2.1
  intro j hj
  simp only [read,tape,map_sub,coeff_mk,cost,mul_zero,zero_add]
  exact add_price (inv_nonneg.mpr (pow_nonneg (pace_pos ..).le _)) (past j hj) (native cover j hj w)
end YM.Integration.WilsonSeparatedPrefixMovingOrdinarySwitch
end
