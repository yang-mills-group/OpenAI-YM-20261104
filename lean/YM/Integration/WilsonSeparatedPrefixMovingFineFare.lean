import YM.Integration.WilsonSeparatedPrefixMovingUnformed

/-! The geometric power at a first exterior contact does not spend one
radius power per perturbative grade. Only the actual engineering weights,
root moment, and the retained spatial moment enter the exponent. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingFineFare
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

theorem powers (u a hull outer target left extra:ℕ)(wave:a=hull+outer+extra)(radius:a=u+outer+target+left)
    (x L T gap z:ℝ)(hx:0<x)(hl:0<L)(hT:0<T)(hgap:0<gap):
    pearlB u a (4*(T*z)) (T*gap/(x*L))*(((x/T)^outer)⁻¹*(x^hull)⁻¹)=
      (T^target)⁻¹*(T^left)⁻¹*x^extra*((16*z)^u*(L/gap)^a):=by
  have rx:x^a=x^hull*x^outer*x^extra:=by rw [wave,pow_add,pow_add]
  have rt:T^a=T^u*T^outer*T^target*T^left:=by rw [radius,pow_add,pow_add,pow_add]
  have bracket:(4*(4*(T*z)))^u=T^u*(16*z)^u:=by rw [←mul_pow];ring
  unfold pearlB
  rw [bracket]
  simp only [mul_pow,div_pow]
  rw [rx,rt]
  field_simp [hl.ne',hx.ne',hT.ne',hgap.ne']

variable {G:Gauge}{H:Hol G}{n e b:ℕ}{E W V:Credit}

def unitFee (Q:SealR G)(X:Q.Rider)(φ:Rarity Q.D)(Z x y B:ℝ):ℝ:=
  (5*radiusH φ x y)^4*(9^b*(B*((polarBill H Q.ans Q.path e b E W V).choose.buy Z*
    WilsonSeparatedPrefixMovingOwnDate.fee Q e X)))

theorem roster (Q:Fin (n+1)→SealR G)(X:Herit Q)(φ:Wilt Q)(Z x y:ℝ)
    (B:Fin (n+1)→ℝ)(k:ℕ):
    nuP (coinMat k e) n (fun i=>WilsonSeparatedPrefixMovingUnformed.fare H E W V
        (Q i) (X i) (φ i) e b Z x y (B i))=
    (x^(∑i,(Q i).h))⁻¹*((coinMat k e)^n * ∏ i, unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=b) (Q i) (X i) (φ i) Z x y (B i)):=by
  simp only [loadRep,WilsonSeparatedPrefixMovingUnformed.fare,WilsonSeparatedPrefixMovingOwnDate.units,
    ←Finset.prod_inv_distrib, Finset.prod_mul_distrib, ←Finset.prod_pow_eq_pow_sum,unitFee]
  ring

end YM.Integration.WilsonSeparatedPrefixMovingFineFare
