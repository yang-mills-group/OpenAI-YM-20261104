import YM.Integration.WilsonSeparatedPrefixMovingMiddleLaw
import YM.Integration.WilsonIndependentMovingRosterAllFineRead

/-! A single normalized scalar up to the actual inner capture. Its raw
value is the full finite N numerator on the nominated cover and old ear. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingBeforeRead
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonIndependentMovingRosterCut (residual parcel located)
open WilsonSeparatedPrefixMovingMiddleLaw (composite)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open Finset
open scoped Classical BigOperators Topology
variable {G:Gauge}{e n:ℕ}{E:Credit}

def scalar (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t b m older N q:ℕ)(ω:Fin 0→YForest G):ℝ:=
  (cruises R.draws R.paid N (F.h+capP Q) N older (agateV
    (current R F ψ Y t N N (y/paceT R.draws.S m t) o) (Ashore Q R.draws R.paid φ X m N N y o))).2 q 0 ω-
      (composite R Q F φ ψ X Y o y t m older N b).2 q 0 ω

theorem heard (e h:ℕ)(T price:ℝ)(f:ℕ→ℝ)(outside:0<T)(grade:∀q≤e,‖f q‖≤(T^h)⁻¹*price):
    Heard e h T price f:=by
  have cash:0≤price:=nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (grade 0 (Nat.zero_le _)))
    (inv_pos.mpr (pow_pos outside _))
  refine ⟨grade,fun g gp small=>⟨?_,fun J=>WilsonSeparatedPrefixMovingHighGrades.original J e h g T price f gp small
    outside cash (fun j _ hj=>grade j hj)⟩⟩
  refine (norm_sum_le ..).trans ?_
  rw [Finset.sum_mul]
  refine sum_le_sum fun j hj=>?_
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg gp _)]
  exact mul_le_mul_of_nonneg_left (grade j (by have h:=mem_range.mp hj;omega)) (pow_nonneg gp _)

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t b m older N h:ℕ)(live:R.anchor ≤ t)(home:t ≤ b)
    (ear:older ≤ b)(fine:b ≤ m)(top:m ≤ N)(ω:Fin 0→YForest G)(A B:ℝ):
    let T:=paceT R.draws.S m t
    let T_b:=paceT R.draws.S b t
    let ratio:=paceT R.draws.S m b
    Heard e h T A (fun q=>(residual R Q F φ ψ X Y o y t m older N).2 q 0 ω) →
    (∀q ≤ e,‖∑d∈range (m-b),WilsonSeparatedPrefixMovingMiddleSector.joined R Q F φ ψ X Y o y t m older N q ω
      (b+d)‖ ≤ (T_b^h)⁻¹*B) →
    Heard e h T (A+ratio^h*B) (fun q=>scalar R Q F φ ψ X Y o y t b m older N q ω):=by
  intro T T_b ratio finer middle
  have positive:0<T:=pace_pos ..
  have div:T/T_b=ratio:=by
    dsimp only [T,T_b,ratio,paceT];field_simp [(R.draws.S.a_pos b).ne',(R.draws.S.a_pos m).ne',(R.draws.S.a_pos t).ne']
  have scale:(T_b^h)⁻¹=(T^h)⁻¹*ratio^h:=by
    rw [←div,div_pow];field_simp [positive.ne',(pace_pos R.draws.S b t).ne']
  have old:=located R Q roster φ X o y m m N (live.trans (home.trans (fine.trans top))) top
  apply heard e h T _ _ positive
  intro q hq
  have law:=WilsonSeparatedPrefixMovingMiddleLaw.original R Q F roster far φ ψ X Y o y t b m older N live home ear fine top q ω
  have first:=finer.1 q hq
  have both:scalar R Q F φ ψ X Y o y t b m older N q ω=
      (residual R Q F φ ψ X Y o y t m older N).2 q 0 ω+
      ∑d∈range (m-b),WilsonSeparatedPrefixMovingMiddleSector.joined R Q F φ ψ X Y o y t m older N q ω (b+d):=by
    rw [←law];dsimp only [scalar,WilsonIndependentMovingRosterCut.residual,composite,Prod.snd_sub,Pi.sub_apply];rw [old];ring
  rw [both]
  exact (norm_add_le ..).trans ((add_le_add first (middle q hq)).trans_eq (by rw [scale];ring))

end YM.Integration.WilsonSeparatedPrefixMovingBeforeRead
