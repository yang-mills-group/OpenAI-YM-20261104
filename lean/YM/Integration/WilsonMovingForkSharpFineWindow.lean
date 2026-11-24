import YM.Integration.WilsonMovingForkSharpFineBirth

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpFineWindow
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open Finset
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}

open WilsonSeparatedPrefixMovingUnformedSector (fresh invoice)
theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(F:SealR G)(k e u target:ℕ)(E W V Wo:Credit):
    let h:=∑j,(Q j).h
    let extra:=u+target+2
    let a:=h+F.h+extra
    ∃C:Credit,∀(R:Realm G (e+1) E)(_P:SpringD R k u a W)(_end:Dormitory R (F.h+h) u Wo)
      (_Q:HorizonP H R W V Q)(_F:PassportC H R F W V)
      (older t m N:ℕ)(_gate:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ m)(_top:m ≤ N)
      (_room:F.h+h ≤ k)(φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)(y g r DF:ℝ)
      (B:Fin (n+1)→ℝ),let T:=paceT R.draws.S m t
      let bill:=invoice Q F X Y e k u a r g DF B
      0 < g → (∀v,Amplitude (φ v) (B v)) → Amplitude ψ DF →
      (∀v,∀p∈tsupport (φ v).ψ.val,∀q∈tsupport ψ.ψ.val,T*g ≤ dist p (T • q)) →
      (∀v,(φ v).radius+|y|+1 ≤ r) → ψ.radius+|y/T|+1 ≤ r →
      ∀(b:ℕ),m ≤ b → b ≤ N → ∀q ≤ e,∀ω:Fin 0→YForest G,
        ∑d∈range (N-b),‖fresh R Q F φ ψ X Y o y t m older N q ω (b+d)‖ ≤
          2*((T^target)⁻¹*bill*(paceT R.draws.S m b)^target)*C.buy (epoch R older b):=by
  intro h extra a
  obtain ⟨C,edge⟩:=WilsonMovingForkSharpFineBirth.original H Q F k e u target E W V Wo
  refine ⟨C.finances 1 le_rfl,?_⟩
  intro R P term aq af older t m N prior home ordered top room φ ψ X Y o y g r DF B T bill gap near far clear roof shade b after cut q grade ω
  let p:=paceT R.draws.S m b
  have pp:0<p:=pace_pos ..
  have ps:p≤1:=pace_le _ after
  let c:=(T^target)⁻¹*bill
  have rp:0≤r:=by linarith only [(φ 0).markG,abs_nonneg y,roof 0]
  have coupon (Q:SealR G)(X:Q.Rider)(f:ℝ)(hf:0≤f):0 ≤ WilsonSeparatedPrefixMovingWages.coupon Q X e (u+a) r f:=by
    have _:0 ≤ WilsonSeparatedPrefixMovingOwnDate.fee Q e X:=by unfold WilsonSeparatedPrefixMovingOwnDate.fee;positivity
    unfold WilsonSeparatedPrefixMovingWages.coupon
    positivity
  have cf:=coupon F Y DF far.1
  have cs:=Finset.prod_nonneg (s:=Finset.univ) fun (j:Fin (n+1)) _=>coupon (Q j) (X j) (B j) (near j).1
  have cm:0≤coinMat k e:=coinMat_nn ..
  have bb:0≤bill:=by dsimp only [bill,invoice];positivity
  have tp:0<T:=pace_pos ..
  have cp:0≤c:=by dsimp [c];positivity
  let z:=fun d:ℕ=>‖fresh R Q F φ ψ X Y o y t m older N q ω (b+d)‖
  have zp:0≤∑d∈range (N-b),z d:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  rw [←Real.norm_of_nonneg zp]
  apply WilsonSeparatedPrefixMovingUnformedCash.calendar R C older b (N-b) prior (home.trans (ordered.trans after))
    (c*p^target) (mul_nonneg cp (pow_nonneg pp.le _)) z
  intro d hd
  let j:=b+d+1
  let z₁:=paceT R.draws.S b j
  have zp₁:0<z₁:=pace_pos ..
  have zs:z₁≤1:=pace_le _ (by dsimp only [j];omega)
  have mult:paceT R.draws.S m j=p*z₁:=by
    dsimp only [z₁,p,paceT]
    field_simp [(R.draws.S.a_pos m).ne',(R.draws.S.a_pos b).ne']
  have rem:p^2*z₁^target≤1:=mul_le_one₀ (pow_le_one₀ pp.le ps) (pow_nonneg zp₁.le _) (pow_le_one₀ zp₁.le zs)
  have decay:(p*z₁)^(target+2) ≤ p^target*z₁^2:=by
    calc _=(p^target*z₁^2)*(p^2*z₁^target):=by rw [mul_pow,pow_add,pow_add];ring
         _ ≤ _:=mul_le_of_le_one_right (by positivity) rem
  have zc:0≤C.buy (epoch R older j):=zero_le_one.trans (C.purchase (window R older b j prior
    (home.trans (ordered.trans after)) (by dsimp only [j];omega)).1)
  have one:=edge R P term aq af older t m N prior home ordered top room φ ψ X Y o y g r DF B gap near far clear roof shade
    (b+d) (by omega) (by omega) q grade ω
  change z d ≤ c*C.buy (epoch R older j)*(paceT R.draws.S m j)^(target+2) at one
  change ‖z d‖ ≤ c*p^target*C.buy (epoch R older j)*z₁^2
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  rw [mult] at one
  exact one.trans ((mul_le_mul_of_nonneg_left decay (mul_nonneg cp zc)).trans_eq (by ring))

end YM.Integration.WilsonMovingForkSharpFineWindow
