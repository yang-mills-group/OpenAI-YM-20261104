import YM.Integration.WilsonOriginalPublicPlantedJoinedCensus
import YM.Integration.WilsonIndependentMatchedCoverJoined
/-! Continue a bought complete signed field below the fitted report. The
quadratically many older dates lie on the same unmarked Wilson course.
An arbitrarily small power of the top mesh pays for all of them once. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedOlderJoin
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentEvenPassport (old count)
open private speed pos scale from YM.Integration.WilsonOriginalPublicPlantedPeriod
open scoped BigOperators Topology Classical

def dates (V:XSpace.Run)(B:ℝ)(i:ℕ):ℝ:=B+(V.reserve:ℝ)*(i:ℝ)^2

theorem credit (V:XSpace.Run)(C:Credit)(B η:ℝ)(finite:0≤B)(small:0<η):
    ∀ᶠ i:ℕ in atTop,C.buy (dates V B i)≤(V.step i).spacing^(-η):=by
  let b:=B+(V.reserve:ℝ)
  have b0:0≤b:=add_nonneg finite (Nat.cast_nonneg _)
  have stop:Tendsto (fun x:ℝ=>x^(2*C.d)*Real.exp (-((η*speed V)*x))) atTop (𝓝 0):=by
    simpa only [Real.rpow_natCast,neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*C.d:ℕ):ℝ) (η*speed V) (mul_pos small (pos V))
  have tail:Tendsto (fun i:ℕ=>C.x*b^C.d*((i:ℝ)^(2*C.d)*Real.exp (-((η*speed V)*i)))) atTop (𝓝 0):=by
    simpa using (stop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (C.x*b^C.d)
  filter_upwards [eventually_ge_atTop (1:ℕ),tail.eventually_le_const zero_lt_one] with i hi paid
  have hi':1≤(i:ℝ):=by exact_mod_cast hi
  have gross:dates V B i ≤ b*(i:ℝ)^2:=by
    unfold dates b
    rw [add_mul]
    gcongr
    exact le_mul_of_one_le_right finite (one_le_pow₀ hi')
  have cp:0≤C.x:=zero_le_one.trans C.good
  have inv:C.buy (dates V B i)*Real.exp (-((η*speed V)*i))≤1:=calc
    _ ≤ C.x*(b*(i:ℝ)^2)^C.d*Real.exp (-((η*speed V)*i)):=by
      unfold Credit.buy
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg finite (by positivity)) gross C.d) cp
    _=C.x*b^C.d*((i:ℝ)^(2*C.d)*Real.exp (-((η*speed V)*i))):=by rw [mul_pow,pow_mul];ring
    _≤1:=paid
  have out:=mul_le_mul_of_nonneg_right inv (Real.exp_pos ((η*speed V)*i)).le
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at out
  rw [Real.rpow_def_of_pos (V.step i).positive,scale]
  rw [show -((i:ℝ)*speed V)*(-η)=(η*speed V)*i by ring]
  exact out

private theorem flatEscort {G:Gauge}{e:ℕ}{E:Credit}(R:Realm G e E){m c:ℕ}
    (live:R.anchor≤ m)(span:m≤ c):Escort R m c (fun _=>1):=by
  refine ⟨live,span,fun _ _ _=>zero_le_one,fun _ _ _=>le_rfl,fun i _ _=>?_⟩
  exact div_le_self zero_le_one (by exact_mod_cast (R.draws.S.block i).pos)

/-- All angular ranks, including each scalar created between report and stop,
of the true repeated normalized conditional on the submitted vacuum. -/
theorem original (G:Gauge)(k e u:ℕ)(E W:Credit)(V:XSpace.Run)(a:ℕ)(B η:ℝ)
    (positive:0≤B)(small:0<η):
    ∀ᶠ i:ℕ in atTop,∀(R:Realm G (e+1) E),Dormitory R k u W →
      ∀ s:ℕ,R.anchor=s → (∀ t ≤ old V a i,R.y (s+t)≤B) →
      ∀ m c:ℕ,m≤ c → c≤old V a i → ∀P:Era G ℝ,Auth k P → ∀ wage:ℝ,Flush e u 1 P wage →
        let read:=cruises R.draws R.paid (s+count V a i) k (s+c) (s+m) P
        let fee:=(V.step i).spacing^(-η)*wage
        Flush e u 1 read fee ∧ ∀ j ≤ e,∀ z:Fin 0→YForest G,‖read.2 j 0 z‖≤fee:=by
  obtain ⟨C,upper⟩:=bulkCert G k e u E W
  filter_upwards [credit V C B η positive small] with i paid R grant s anchor home m c mc cm P auth wage filed read fee
  have jpos:0≤(V.reserve:ℝ)*(i:ℝ)^2:=by positivity
  have nd : (old V a i:ℝ) ≤ (V.reserve:ℝ)*(i:ℝ)^2:=by
    rw [sq,←mul_assoc]
    exact_mod_cast (Nat.div_le_self (V.reserve*i*i) a)
  have cpos:c≤ count V a i:=cm.trans (Nat.le_add_right ..)
  have mg:Escort R (s+m) (s+c) (fun _=>1):=flatEscort R (anchor ▸ Nat.le_add_right ..) (Nat.add_le_add_left mc s)
  have room:PadRank R (s+m) (s+c) (dates V B i):=by
    refine ⟨?_,?_⟩
    · intro t lo hi
      have ts : t=s+(t-s):=by omega
      calc R.y t = R.y (s+(t-s)):=congrArg R.y ts
           _ ≤ B:=home _ (by omega)
           _ ≤ _:=le_add_of_nonneg_right jpos
    · have step:s+c-(s+m)≤old V a i:=by omega
      exact (Nat.cast_le.mpr step).trans (nd.trans (le_add_of_nonneg_left positive))
  have earned:Flush e u 1 read fee:=by
    refine ⟨mul_nonneg (Real.rpow_nonneg (V.step i).positive.le _) filed.1,?_⟩
    intro j hj r _
    exact (upper j hj r R grant (s+m) (s+c) (fun _=>1) (s+count V a i) (dates V B i)
      mg room (Nat.add_le_add_left cpos s) P wage auth filed.1 filed.2).more (mul_le_mul_of_nonneg_right paid filed.1)
  exact ⟨earned,fun j hj=>WilsonIndependentMatchedCoverJoined.unit earned j hj⟩

end YM.Integration.WilsonOriginalPublicPlantedOlderJoin
