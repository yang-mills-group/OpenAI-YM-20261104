import YM.Integration.WilsonIndependentMatchedOwnHomeSharpShell
import YM.Integration.WilsonMovingForkSharpExteriorIncome

/-! The optical debit on the far field in the joined K-born estimate. Both
occurrences of its full reversion cancel the geometric divisor. The only
explicit residual positive power of the home ratio is the field's own grade. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeFixedPower
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentMovingRosterBirthCalendar (room)
open WilsonIndependentMatchedOwnHomeFundedPrefix (fare)
open WilsonIndependentMatchedOwnHomeKShell (Coins rider cost)
open scoped BigOperators Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{e d n:ℕ}

theorem unformed (R:Realm G (e+1) C)(Q:Fin (n+1)→SealR G)(F:SealR G)(X:Herit Q)(Y:F.Rider)
    (first shape chron:Credit)(p m older:ℕ)(width r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ)(a:Alma F.F):
    fare R Q F X Y first shape chron p m older width r gap farGap DF B=
    fee F e Y*fare R Q F X (axis F a) first shape chron p m older width r gap farGap DF B:=by
  simp only [fare,WilsonSeparatedPrefixMovingUnformedSector.invoice,WilsonIndependentMovingRosterInvoice.charge,
    WilsonSeparatedPrefixMovingWages.coupon,WilsonMovingForkSharpExteriorIncome.axis_paid]
  ring

def rent (book:Coins)(H:Hol G)(R:Realm G (e+1) C)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (X:Herit Q)(a:Alma F.F)(ψ:Rarity F.D)(Φ:Rarity d)(y amp:ℝ)(older t b m K p ex:ℕ)
    (r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ)(ρ upper stipend:ℝ):ℝ:=
  let T:=paceT R.draws.S m t
  let δ:=paceT R.draws.S m K
  let z:=paceT R.draws.S m b
  let volume:=(5*radiusH Φ (paceT R.draws.S t b) y)^4*amp
  let approach:=fare R Q F X (axis F a) book.first book.shape book.chron p m older z r gap farGap DF B
  let pay:=WilsonIndependentMatchedOwnHomeDeposit.price F (capP Q) e book.forward book.inverse book.terminal
    (polarBill H F.ans F.path e 0 C C C).choose R.draws.S R.y t m K older ψ z DF
  let held:=2*book.reach.buy (epoch R m K)*(book.near.buy (room r gap z)*WilsonIndependentMovingRosterBirth.charge Q X e B)
  upper+|ρ^4| *((T^p)⁻¹*(stipend*|volume*approach|)+volume*(T^F.h*δ^ex*pay*held))

private lemma cancel {A x y v:ℝ}(Apos:0<A)(xpos:0 ≤ x)(gate:x ≤ A*v):(A⁻¹)*(x*y) ≤ v*|y|:=by
  calc
    _ ≤ A⁻¹*(x*|y|):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) xpos) (inv_nonneg.mpr Apos.le)
    _ ≤ A⁻¹*((A*v)*|y|):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right gate (abs_nonneg _)) (inv_nonneg.mpr Apos.le)
    _ = v*|y|:=by field_simp

theorem original (H:Hol G)(F:SealR G)(e:ℕ)(W:Credit):
    ∃P₁ P₂:Credit,∀(R:Realm G (e+1) C)(_forward:AheadT H R C C F W)
    (book:Coins)(Q:Fin (n+1)→SealR G)(X:Herit Q)(a:Alma F.F)(ψ:Rarity F.D)(Φ:Rarity d)
    (y amp:ℝ)(older t b m K N p ex:ℕ),R.anchor ≤ t → t ≤ m → m ≤ N →
    ∀(r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ)(ρ upper:ℝ),
    let T:=paceT R.draws.S m t
    let stipend:=((Fintype.card (Alma F.F):ℝ)^2*(e+1))*P₁.buy (Compar R.draws.S R.y t m)*P₂.buy (R.y m)
    cost book H R Q F X a ψ Φ y amp older t b m K N p ex r gap farGap DF B ρ (T^F.h*upper) ≤
      rent book H R Q F X a ψ Φ y amp older t b m K p ex r gap farGap DF B ρ upper stipend:=by
  obtain ⟨P₁,P₂,issued⟩:=WilsonIndependentMatchedOwnHomeAxisWage.original H F e C C C W
  refine ⟨P₁,P₂,?_⟩
  intro R forward book Q X a ψ Φ y amp older t b m K N p ex live asc top r gap farGap DF B ρ upper T stipend
  have mon:fee F e (rider R F N t m a) ≤ T^F.h*stipend:=by
    exact (issued R forward t m N live asc top a).trans_eq (by dsimp only [stipend,T];ring)
  have Tpos:0<T:=pace_pos ..
  dsimp only [cost,rent]
  rw [unformed R Q F X (rider R F N t m a) book.first book.shape book.chron p m older (paceT R.draws.S m b) r gap farGap DF B a]
  rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero F.h Tpos.ne'),one_mul]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply add_le_add_left
  let u:=(5*radiusH Φ (paceT R.draws.S t b) y)^4*amp
  let pay:=fare R Q F X (axis F a) book.first book.shape book.chron p m older (paceT R.draws.S m b) r gap farGap DF B
  change (T^F.h)⁻¹*((T^p)⁻¹*(u*(fee F e (rider R F N t m a)*pay))) ≤ (T^p)⁻¹*(stipend*|u*pay|)
  calc
    _=(T^p)⁻¹*((T^F.h)⁻¹*(fee F e (rider R F N t m a)*(u*pay))):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (cancel (y:=u*pay) (pow_pos Tpos F.h) (WilsonMovingForkSharpExteriorIncome.nonnegative F e (rider R F N t m a)) mon) (by positivity)
end YM.Integration.WilsonIndependentMatchedOwnHomeFixedPower
end
