import YM.Integration.WilsonIndependentMovingRosterBirth
import YM.Integration.WilsonSeparatedPrefixMovingLocator

/-! Carry the complete near birth on the same deposited field to the fine
child of the next exterior contact. A single age price covers the actual
first production and the subsequent unmarked transfer of that deposit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterBirthReceipt
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMovingRosterBirth (charge)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}

/-- This is the unaltered joint first difference. Its two terms use the
true normalized incoming and outgoing full products on that same chart. -/
theorem first {e:ℕ}{E W V:Credit}{H:Hol G}(R:Realm G (e+1) E)
    (Q:Fin (n+1)→SealR G)(paid:HorizonP H R W V Q)(φ:Wilt Q)(X:Herit Q)
    (m j N:ℕ)(y:ℝ)(o:CellR)(start:R.anchor ≤ m)(before:m ≤ j)(live:j < N):
    Ash R.draws R.paid φ X m j N y o =
      verseI R.draws R.paid j N (capP Q) (Ashore Q R.draws R.paid φ X m (j+1) N y o) -
      Ashore Q R.draws R.paid φ X m j N y o:=
  ash_tide paid φ X start before live o

theorem carried (H:Hol G)(Q:Fin (n+1)→SealR G)(E W V S U:Credit)(e u extra:ℕ):
    ∃C:Credit,∀(R:Realm G (e+1) E),HorizonP H R W V Q →
    SpringD R (capP Q) u (capP Q+(u+extra)) S → Dormitory R (capP Q) u U →
    ∀(m i j N:ℕ)(φ:Wilt Q)(X:Herit Q)(B:Fin (n+1)→ℝ)(Z y:ℝ)(o:CellR),
    R.anchor ≤ m → m ≤ i → i < j → j < N → Compar R.draws.S R.y m (j+1) ≤ Z →
    PadRank R (i+1) j Z → Bough Q φ y Z B →
    let w:=paceT R.draws.S m (j+1)
    let D:=Ash R.draws R.paid φ X m j N y o
    let Y:=cruises R.draws R.paid N (capP Q) j (i+1) D
    let money:=C.buy Z*w^extra*charge Q X e B
    Auth (capP Q) Y ∧ Flush e u 1 Y money ∧
      ∀(d:ℕ)(χ:Rarity d)(P:Patch)(x y':ℝ)(o':CellR),(0:Cover)∈VisitsT χ x y' o' →
        Income Y (capP Q) e u (OrbP P χ x y' o') ((9:ℝ)^u*money):=by
  obtain ⟨orig,birth⟩:=WilsonIndependentMovingRosterBirth.original H Q E W V S e u extra
  obtain ⟨down,deliver⟩:=waveSeen G (capP Q) e u E U
  refine ⟨down.prodC orig,?_⟩
  intro R home spring dorm m i j N φ X B Z y o start before later inside clock rent geo w D Y money
  have bought:=birth R home spring m j N φ X B Z y o start (before.trans later.le) inside clock geo
  have escort:Escort R (i+1) j (fun _=>1):=by
    refine ⟨start.trans (before.trans (Nat.le_succ i)),later,fun _ _ _=>zero_le_one,fun _ _ _=>le_rfl,?_⟩
    intro j' _ _
    exact div_le_self zero_le_one (by exact_mod_cast (R.draws.S.block j').pos)
  have income:=deliver R dorm (i+1) j (fun _=>1) j N N _ (max 0 (R.tempC j j)) Z
    escort rent le_rfl inside.le inside.le (le_max_right _ _) D D
    (Fringed.same bought.2.2 bought.1 (le_max_left _ _))
  have priced:Flush e u 1 Y money:=by
    change Flush e u 1 Y ((down.prodC orig).buy Z*w^extra*charge Q X e B)
    rw [Credit.products,mul_assoc (down.buy Z),mul_assoc (down.buy Z)]
    exact income.f_l
  exact ⟨income.pen,priced,fun d χ P x y' o' located=>
    WilsonSeparatedPrefixMovingOldPair.rooted income.pen priced P χ x y' o' located⟩

/-- A real zero-site locator is available for every actual cell translation.
Its profile is used only at the next joining date. -/
theorem center {e u:ℕ}{l:ℕ}{Y:Era G ℝ}{money:ℝ}(alive:Auth l Y)(rent:Flush e u 1 Y money)
    (P:Patch)(x y:ℝ)(o:CellR)(positive:0 < x):
    Income Y l e u (OrbP P (WilsonSeparatedPrefixMovingLocator.booked y o) x y o) ((9:ℝ)^u*money):=
  WilsonSeparatedPrefixMovingOldPair.rooted alive rent P _ x y o (WilsonSeparatedPrefixMovingLocator.site x y o positive)

end YM.Integration.WilsonIndependentMovingRosterBirthReceipt
