import YM.Integration.WilsonIndependentMovingRosterAllFinePlate
import YM.Integration.WilsonIndependentFittedEarlyGeometry

/-! Optical age and its finite-order costs on every part of the very
two-length board used for the signed moving scalar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterAllFineAge
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RegulatorIR RegulatorIR.Ledger
open WilsonIndependentEvenPassport (old young count)
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentFittedEarlyGeometry (block height payment)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E:Credit}

def size (V:XSpace.Run)(a:ℕ)(B:ℝ):ℝ:=
  max 1 B+4*(V.reserve:ℝ)*Real.log ((V.ratio^(2*a):ℕ):ℝ)

theorem quadratic (V:XSpace.Run)(a phase:ℕ)(ha:0 < a)(hj:4 ≤ phase)(i:Requests a)(A:Levels G)(s:ℕ)
    (acts:∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i →
      (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
        (WilsonIndependentExactPlate.S V a ha phase hj).pactP f)
    (R:Realm G e E)(draw:R.draws=A)(B:ℝ)(older m:ℕ)
    (start:s ≤ older)(ordered:older ≤ m)(top:m ≤ s+count V a i.val)(home:R.y older ≤ B):
    epoch R older m ≤ size V a B*(i.val:ℝ)^2:=by
  let n:=count V a i.val
  let c:=Real.log ((V.ratio^(2*a):ℕ):ℝ)
  have i1:1 ≤ i.val:=ha.trans_le i.prop
  have ii:1 ≤ (i.val:ℝ):=by exact_mod_cast i1
  have shot:1 ≤ (i.val:ℝ)^2:=one_le_pow₀ ii
  have l1:1 ≤ V.ratio:=by have:=V.large;omega
  have cpos:0 ≤ c:=Real.log_nonneg (by exact_mod_cast (Nat.one_le_pow (2*a) V.ratio l1))
  have hi:=height A.S s n c (fun j hj' => by
    apply Real.log_le_log (by exact_mod_cast (A.S.block (s+j)).pos)
    exact_mod_cast block V a phase ha hj i A s acts (s+j) (Nat.le_add_right ..) (Nat.add_lt_add_left hj' s))
  have uv:i.val ≤ V.reserve*i.val*i.val:=by
    have t:1 ≤ V.reserve*i.val:=Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have h:=V.spare;omega) (by omega))
    simpa using Nat.mul_le_mul_right i.val t
  have days:n ≤ 2*(V.reserve*i.val*i.val):=by
    change (V.reserve*i.val*i.val)/a+i.val/a ≤ _
    have f:=Nat.div_le_self (V.reserve*i.val*i.val) a
    have g:=Nat.div_le_self i.val a
    omega
  have dates:(n:ℝ) ≤ 2*(V.reserve:ℝ)*(i.val:ℝ)^2:=by
    have cost:=Nat.cast_le (α:=ℝ).mpr days
    simpa only [Nat.cast_mul,Nat.cast_ofNat,pow_two,mul_assoc] using cost
  have lower:=scales A.S start
  have newer:=scales A.S top
  have wage:=mul_le_mul_of_nonneg_right dates cpos
  have cap:B ≤ max 1 B*(i.val:ℝ)^2:=(le_max_right ..).trans
    (le_mul_of_one_le_right (zero_le_one.trans (le_max_left ..)) shot)
  unfold WilsonSeparatedPrefixMovingCalendar.epoch
  rw [draw]
  change R.y older+2*(A.S.scale m-A.S.scale older) ≤ (max 1 B+4*(V.reserve:ℝ)*c)*(i.val:ℝ)^2
  have near:=scales A.S ordered
  nlinarith only [home,cap,lower,newer,hi,wage,near]

theorem original (V:XSpace.Run)(a phase:ℕ)(ha:0 < a)(hj:4 ≤ phase)(C:Credit)(B η:ℝ)(small:0 < η):
    ∀ᶠ j:ℕ in atTop,∀i:Requests a,i.val=j → ∀(A:Levels G)(s:ℕ),
    (∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i →
      (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
        (WilsonIndependentExactPlate.S V a ha phase hj).pactP f) →
    ∀(R:Realm G e E),R.draws=A → R.anchor=s → ∀older m:ℕ,s ≤ older → older ≤ m → m ≤ s+count V a i.val → R.y older ≤ B →
      C.buy (epoch R older m) ≤ (V.step j).spacing^(-η):=by
  filter_upwards [payment V C (size V a B) η small] with j paid i same A s acts R draw anchor older m lo mid hi home
  have live:R.anchor ≤ older:=anchor ▸ lo
  apply paid _ (zero_le_one.trans (window R older older m live le_rfl mid).1)
  simpa only [same] using quadratic V a phase ha hj i A s acts R draw B older m lo mid hi home

/-- The portion of an older calendar beyond the chosen exterior keeps its
own physical scale ratio. The top cutoff does not enter either ratio. -/
theorem rulers (R:Realm G e E)(older t m:ℕ):
    epoch R older m=R.y older+2*(Real.log (paceT R.draws.S m t)+Real.log (paceT R.draws.S t older)):=by
  rw [WilsonSeparatedPrefixMovingCalendar.epoch,pace_rep,pace_rep,Real.log_exp,Real.log_exp]
  ring

end YM.Integration.WilsonIndependentMovingRosterAllFineAge

