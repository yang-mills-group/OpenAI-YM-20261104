import YM.Integration.WilsonIndependentMatchedOwnHomeBornRaw
import YM.Integration.WilsonIndependentMatchedOwnHomeFundedPrefix
import YM.Integration.WilsonIndependentMatchedOwnHomeInteriorSale

/-! The measured high shell of the actual K-born joint detector on the older
χ-vacuum. Both differences from the χ-born native raw row are paid on this
same elected course, with its own registered far input and optical homes. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeKShell
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
open WilsonIndependentMatchedOwnHomeBornRaw (measured)
open scoped BigOperators Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{n e d height seats:ℕ}

structure Coins where
  clock:Credit
  first:Credit
  shape:Credit
  chron:Credit
  forward:Credit
  inverse:Credit
  terminal:Credit
  near:Credit
  reach:Credit

def rider (R:Realm G (e+1) C)(F:SealR G)(N t m:ℕ)(a:Alma F.F):F.Rider:=
    PermuteLens R.draws R.paid F N t (brought R.draws R.paid F N t m (axis F a))

def cost (book:Coins)(H:Hol G)(R:Realm G (e+1) C)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (X:Herit Q)(a:Alma F.F)(ψ:Rarity F.D)(Φ:Rarity d)(y amp:ℝ)(older t b m K N p ex:ℕ)
    (r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ)(ρ upper:ℝ):ℝ:=
  let T:=paceT R.draws.S m t
  let δ:=paceT R.draws.S m K
  let z:=paceT R.draws.S m b
  let volume:=(5*radiusH Φ (paceT R.draws.S t b) y)^4*amp
  let approach:=WilsonIndependentMatchedOwnHomeFundedPrefix.fare R Q F X (rider R F N t m a)
    book.first book.shape book.chron p m older z r gap farGap DF B
  let pay:=WilsonIndependentMatchedOwnHomeDeposit.price F (capP Q) e book.forward book.inverse book.terminal
    (polarBill H F.ans F.path e 0 C C C).choose R.draws.S R.y t m K older ψ z DF
  let held:=2*book.reach.buy (epoch R m K)*(book.near.buy (room r gap z)*WilsonIndependentMovingRosterBirth.charge Q X e B)
  (T^F.h)⁻¹*upper+|ρ^4| *((T^F.h)⁻¹*((T^p)⁻¹*(volume*approach))+volume*(T^F.h*δ^ex*pay*held))

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(F:SealR G)(e p ex:ℕ)(positive:0<p)
    (gain:2 ≤ F.h+ex)(near:∀s,Named M height seats (Q s))(far:Named M height seats F)
    (capacity:needed (F.h+capP Q) 0 p ≤ seats)(reserve:capP Q+F.h+ex ≤ seats)(W:Credit):
    ∃book:Coins,∀(R:Realm G (e+1) C)(_stock:Elected M R height seats)(_forward:AheadT H R C C F W)
    (older t b m K N:ℕ),R.anchor ≤ older → older ≤ t → t ≤ b → b ≤ m → m ≤ K → K ≤ N →
    ∀(α:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(a:Alma F.F)(r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ)
      (Φ:Rarity d)(y amp:ℝ)(o:CellR)(w:Fin 0→YForest G),
      Clear R Q F α ψ older t b m r gap farGap DF B → Amplitude Φ amp →
    ∀(J:ℕ)(g ρ upper:ℝ),J ≤ e → |g| ≤ 1 →
    let Y:=rider R F N t m a
    (∀l ≤ e,‖ρ^4*raw R Q F α ψ X Y Φ y o t m b older N l 0 w‖ ≤ upper) →
    ‖measured R Q F α ψ X Y Φ y o t m b older K N e g ρ w-
     measured R Q F α ψ X Y Φ y o t m b older K N J g ρ w‖ ≤
    (Finset.Ico (J+1) (e+1)).card*|g|^(J+1)*((e+1)*book.clock.buy (Compar R.draws.S R.y older m)*
      cost book H R Q F X a ψ Φ y amp older t b m K N p ex r gap farGap DF B ρ upper):=by
  obtain ⟨clock,report⟩:=WilsonIndependentMatchedOwnHomeBornRaw.paid (D:=d) (n:=n) H F e C C C
  obtain ⟨first,shape,chron,suffix⟩:=WilsonIndependentMatchedOwnHomeFundedPrefix.original (d:=d) M Q F e p positive near far capacity
  obtain ⟨forward,inverse,terminal,regional,reach,interior⟩:=
    WilsonIndependentMatchedOwnHomeInteriorSale.original (d:=d) H Q F e ex gain C C C W C C C
  let book:Coins:=⟨clock,first,shape,chron,forward,inverse,terminal,regional,reach⟩
  refine ⟨book,?_⟩
  intro R stock direction older t b m K N awake start atFar middle cut top α ψ X a r gap farGap DF B Φ y amp o w geometry volume J g ρ upper order small Y ceiling
  have oldm:=start.trans (atFar.trans middle)
  have past:=suffix R stock older t b m K N awake start atFar middle cut top α ψ X Y r gap farGap DF B Φ y amp o w geometry volume
  obtain ⟨roster,_⟩:=WilsonIndependentMovingRosterAllFineSeats.roster stock Q F near far
  have native:=interior R roster direction (stock.spring _ _ _ (by omega) (by omega) (by omega))
    (stock.dorm _ _ (by omega) (by omega)) (stock.dorm _ _ (by omega) (by omega))
    older t b m K N awake start atFar middle cut top α ψ X a Φ amp DF y (room r gap (paceT R.draws.S m b)) B o volume geometry.2.2.2.1
  have cover:=WilsonIndependentMovingRosterBirthCalendar.geometry Q α B r gap (paceT R.draws.S m b) geometry.1 geometry.2.2.1
    (fun s=>by have hh:=geometry.2.2.2.2.2.1 s;have nn:=abs_nonneg (paceT R.draws.S m b); linarith) geometry.2.2.2.2.1
  exact report R direction.p Q α ψ X Y Φ y o t m b older K N awake oldm cut top J g ρ _ _ _ w order small ceiling past
    (fun j hj=>native cover j hj w)
end YM.Integration.WilsonIndependentMatchedOwnHomeKShell
end
