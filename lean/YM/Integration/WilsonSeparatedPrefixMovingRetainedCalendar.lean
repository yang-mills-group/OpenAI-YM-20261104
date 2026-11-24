import YM.Integration.WilsonSeparatedPrefixMovingCalendar

/-! The squared chronological credit buys half a mesh power. The remaining power is summable at every true first-joining date. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingRetainedCalendar
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window credit light)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E:Credit}

open Finset

def reserve (C:Credit):Credit:=(C.prodC C).finances 1 le_rfl

theorem half (R:Realm G e E)(C:Credit)(host H j:ℕ)(live:R.anchor ≤ host)(base:host ≤ H)(cut:H ≤ j):
    C.buy (epoch R host j)*Real.sqrt (paceT R.draws.S H j) ≤ (reserve C).buy (epoch R host H):=by
  let x:=paceT R.draws.S H j
  let A:=(reserve C).buy (epoch R host H)
  let B:=C.buy (epoch R host j)
  have xp:0<x:=pace_pos ..
  have ap:1 ≤ A:=(reserve C).purchase (window R host H H live base le_rfl).1
  have bp:0 ≤ B:=zero_le_one.trans (C.purchase (window R host H j live base cut).1)
  have closed:=credit R (C.prodC C) host H j live base cut
  rw [Credit.products] at closed
  have bill:B^2*x ≤ A:=by
    apply (le_of_mul_le_mul_right ?_ xp)
    change (B^2*x)*x ≤ A*x
    simpa only [A,B,x,reserve,pow_two,mul_assoc] using closed
  have sq:(B*Real.sqrt x)^2 ≤ A:=by
    rw [mul_pow,Real.sq_sqrt xp.le];exact bill
  change B*Real.sqrt x ≤ A
  nlinarith [mul_nonneg (sub_nonneg.mpr ap) (zero_le_one.trans ap),sq_nonneg (B*Real.sqrt x-A)]

theorem original (R:Realm G e E)(C:Credit)(m H n:ℕ)(live:R.anchor ≤ m)(base:m ≤ H)(v:ℝ)(room:3/2 ≤ v):
    ∑d∈range n,C.buy (epoch R m (H+d+1))*(paceT R.draws.S m (H+d+1))^v ≤
      2*(reserve C).buy (epoch R m H)*(paceT R.draws.S m H)^v:=by
  let A:=(reserve C).buy (epoch R m H)
  let δ:=paceT R.draws.S m H
  have ap:0 ≤ A:=zero_le_one.trans ((reserve C).purchase (window R m H H live base le_rfl).1)
  have dp:0 ≤ δ^v:=Real.rpow_nonneg (pace_pos ..).le v
  have each (d:ℕ):
      C.buy (epoch R m (H+d+1))*(paceT R.draws.S m (H+d+1))^v ≤
        (δ^v*A)*paceT R.draws.S H (H+d):=by
    let j:=H+d+1
    let x:=paceT R.draws.S H j
    let price:=C.buy (epoch R m j)
    have date:H ≤ j:=by dsimp only [j];omega
    have p0:0 ≤ price:=zero_le_one.trans (C.purchase (window R m H j live base date).1)
    have xp:0 < x:=pace_pos ..
    have x1:x ≤ 1:=pace_le _ date
    have split:paceT R.draws.S m j=δ*x:=by unfold δ x paceT;field_simp [(R.draws.S.a_pos H).ne',(R.draws.S.a_pos m).ne']
    have power:x^v ≤ Real.sqrt x*x:=by
      calc
        _ ≤ x^((1:ℝ)/2+1):=Real.rpow_le_rpow_of_exponent_ge xp x1 (by linarith)
        _=Real.sqrt x*x:=by rw [Real.rpow_add xp,←Real.sqrt_eq_rpow,Real.rpow_one]
    have wage:=half R C m H j live base date
    have fine:x ≤ paceT R.draws.S H (H+d):=div_le_div_of_nonneg_right
      (R.draws.S.strictAnti.antitone (Nat.le_succ _)) (R.draws.S.a_pos _).le
    change price*(paceT R.draws.S m j)^v ≤ _
    rw [split,Real.mul_rpow (pace_pos ..).le xp.le]
    calc
      _=δ^v*(price*x^v):=by ring
      _ ≤ δ^v*(A*x):=by
        apply mul_le_mul_of_nonneg_left _ dp
        exact (mul_le_mul_of_nonneg_left power p0).trans (by
          rw [←mul_assoc];exact mul_le_mul_of_nonneg_right wage xp.le)
      _ ≤ _:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_left fine (mul_nonneg dp ap)
  calc
    _ ≤ ∑d∈range n,(δ^v*A)*paceT R.draws.S H (H+d):=sum_le_sum fun d _=>each d
    _=(δ^v*A)*∑d∈range n,paceT R.draws.S H (H+d):=by rw [mul_sum]
    _ ≤ _:=((mul_le_mul_of_nonneg_left (light R.draws.S H n) (mul_nonneg dp ap))).trans_eq (by dsimp only [A,δ];ring)

end YM.Integration.WilsonSeparatedPrefixMovingRetainedCalendar
