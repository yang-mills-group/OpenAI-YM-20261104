import YM.Integration.WilsonIndependentMatchedCoverCap

/-! When different positions carry stable remainders, their gains multiply.
All external and engineering factors remain the original per-site factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterPowers
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
variable {I:Type*}
theorem wages (a:Finset I)(d w:I→ℕ)(Z:I→ℝ)(δ x:ℝ)(hd:0<δ)(hx:0<x):
    (∏s∈a,Z s*((x^(d s))⁻¹*(δ/x)^((w s:ℝ)/4)))=
    (∏s∈a,Z s)*(x^(∑s∈a,d s))⁻¹*(δ/x)^((((∑s∈a,w s):ℕ):ℝ)/4) := by
  classical
  induction a using Finset.induction_on with
  | empty=>simp
  | @insert s a h ih=>
    simp only [Finset.prod_insert h,Finset.sum_insert h,Nat.cast_add,add_div,pow_add,
      _root_.mul_inv_rev,Real.rpow_add (div_pos hd hx),ih]
    ring

variable {u b n k e:ℕ}
def profiles (n k e u b:ℕ)(t z Z:ℝ):ℝ:=(n:ℝ)*(coinMat k e+1)^n*(t^b)⁻¹*(16*z)^u*Z

theorem bill (C S:ℝ)(d w:ℕ)(δ x L t z Z:ℝ)(hx:0<x)(hL:0<L)(hd:0<δ)(ht:0<t):
    let r:=x*L
    let α:ℝ:=(w:ℝ)/4
    C*((n:ℝ)*S*pearlB u b (4*z) (t/r)*((coinMat k e+1)^n*
      (Z*(x^d)⁻¹*(δ/x)^α)))=(C*S*(L^d*L^α))*profiles n k e u b t z Z*
        r^((b:ℝ)-(d:ℝ))*(δ/r)^α:=by
  dsimp only
  rw [Real.rpow_sub (mul_pos hx hL),Real.rpow_natCast,Real.rpow_natCast,
    ←div_div δ x L,Real.div_rpow (div_nonneg hd.le hx.le) hL.le]
  unfold pearlB profiles
  rw [show 4*(4*z)=16*z by ring,div_pow,mul_pow,mul_pow]
  field_simp [hx.ne',hL.ne',ht.ne',(Real.rpow_pos_of_pos hL ((w:ℝ)/4)).ne']
  ring

end YM.Integration.WilsonIndependentMatchedRosterPowers

