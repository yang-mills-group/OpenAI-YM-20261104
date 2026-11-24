import YM.Integration.WilsonSeparatedPrefixMovingPaidPair
import YM.Integration.WilsonSeparatedPrefixMovingNextCalendar
import YM.Integration.WilsonSeparatedPrefixMovingLocator
import YM.Integration.WilsonIndependentMatchedVacant

/-! The cutoff-uniform complete two-birth sector for a normalized near pair
and one original distant field at its own reporter. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPairSector
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open Finset
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{e:ℕ}{E:Credit}

def current (R:Realm G (e+1) E)(Q:SealR G)(φ:Rarity Q.D)(X:Q.Rider)(m i N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  locale o (Q.spins R.draws R.paid φ m i N y X)

lemma vacant (R:Realm G (e+1) E)(Q:SealR G)(φ:Rarity Q.D)(X:Q.Rider)(m i N:ℕ)(y:ℝ)(o:CellR)
    (miss:¬(VisitsT φ (paceT R.draws.S m i) y o).Nonempty):current R Q φ X m i N y o=0:=by
  unfold current SealR.spins FirstCharge
  rw [pupil_eye _ _ _ _ _ _ (pace_pos ..),Finset.not_nonempty_iff_eq_empty.mp miss,sum_empty]

def nested (R:Realm G (e+1) E)(A B F:SealR G)(φ:Rarity A.D)(ψ:Rarity B.D)(χ:Rarity F.D)
    (X:A.Rider)(Y:B.Rider)(Z:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)(i j:ℕ):ℝ:=
  let head:=current R A φ X m (j+1) N y o
  let tail:=current R B ψ Y m (j+1) N y o
  let far:=current R F χ Z t (i+1) N (y / paceT R.draws.S m t) o
  let pair:=cruises R.draws R.paid N (A.h+B.h) j (i+1) (JoinGap R.draws R.paid j N A.h B.h head tail)
  if i < j then (cruises R.draws R.paid N (F.h+(A.h+B.h)) i older
    (JoinGap R.draws R.paid i N F.h (A.h+B.h) far pair)).2 q 0 ω else 0

def tariff (A B F:SealR G)(X:A.Rider)(Y:B.Rider)(Z:F.Rider)(e u a ai:ℕ)(r v d g DA D_B DF:ℝ):ℝ:=
  (9:ℝ)^(u+a)*(16*v)^u*(g⁻¹)^a*(16*r)^(u+a)*(d⁻¹)^ai*
    (WilsonSeparatedPrefixMovingWages.coupon A X e (u+a+ai) r DA*
     WilsonSeparatedPrefixMovingWages.coupon B Y e (u+a+ai) r D_B*
     WilsonSeparatedPrefixMovingWages.coupon F Z e (u+a) v DF)

private lemma wealth (A:SealR G)(X:A.Rider)(u:ℕ)(z B:ℝ)(h:0 ≤ B):
    0 ≤ WilsonSeparatedPrefixMovingWages.coupon A X e u z B:=by
  have paid:0 ≤ WilsonSeparatedPrefixMovingOwnDate.fee A e X:=by unfold WilsonSeparatedPrefixMovingOwnDate.fee;positivity
  unfold WilsonSeparatedPrefixMovingWages.coupon;positivity

private lemma cap {D:ℕ}(φ:Rarity D){x y b:ℝ}(positive:0 ≤ x)(small:x ≤ 1)(roof:φ.radius+|y|+1 ≤ b):
    radiusH φ x y ≤ b:=by unfold radiusH;rw [abs_of_nonneg positive];linarith only [small,roof]

theorem original (H:Hol G)(A B F:SealR G)(k e u target:ℕ)(pos:0 < target)(E W V Wd Wo:Credit):
    let extra:=u+target
    let a:=F.h+extra
    let ai:=B.h+A.h+(u+a+2)
    ∃C:Credit,∀(R:Realm G (e+1) E)(_Po:SpringD R k u a W)(_Pi:SpringD R k (u+a) ai W)
      (_Pd:Dormitory R (A.h+B.h) (u+a) Wd)(_Pe:Dormitory R (F.h+(A.h+B.h)) u Wo)
      (_A:PassportC H R A W V)(_B:PassportC H R B W V)(_F:PassportC H R F W V)
      (older t m N:ℕ)(_born:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ m)(_top:m ≤ N)
      (_room:F.h+(A.h+B.h) ≤ k)(φ:Rarity A.D)(ψ:Rarity B.D)(χ:Rarity F.D)(X:A.Rider)(Y:B.Rider)(Z:F.Rider)
      (o:CellR)(y near far r v DA D_B DF:ℝ),
      let T:=paceT R.draws.S m t
      let price:=tariff A B F X Y Z e u a ai r v near far DA D_B DF
      Amplitude φ DA → Amplitude ψ D_B → Amplitude χ DF → 0 < near → 0 < far →
      (∀p∈tsupport ψ.ψ.val,∀b∈tsupport φ.ψ.val,near ≤ dist p b) →
      (∀q∈tsupport χ.ψ.val,T*far+1+|y| ≤ ‖T • q‖) →
      φ.radius+|y|+1 ≤ r → ψ.radius+|y|+1 ≤ r → 2+2*|y| ≤ v → χ.radius+|y/T|+1 ≤ v →
      ∀q ≤ e,∀ω:Fin 0→YForest G,
        ‖∑i∈range (N-m),∑j∈(range (N-m)).filter (fun j=>i ≤ j),
          nested R A B F φ ψ χ X Y Z o y t m older N q ω (m+i) (m+j)‖ ≤ 4*((T^target)⁻¹*price)*C.buy (epoch R older m):=by
  intro extra a ai
  obtain ⟨C,fees⟩:=WilsonSeparatedPrefixMovingPaidPair.original (H:=H) A B F k e u a ai target 0
    extra 2 0 rfl (by dsimp only [a,extra];omega) rfl E W V Wd Wo
  refine ⟨C.finances 1 le_rfl,?_⟩
  intro R Po Pi Pd Pe PA PB PF older t m N born start home top room φ ψ χ X Y Z o y near far r v DA D_B DF
    T price ampA ampB ampE nearPos farPos innerGap farAway rA rB vC vE q hq ω
  have om:older ≤ m:=start.trans home
  have tpos:0 < T:=pace_pos .. 
  have tlarge:1 ≤ T:=pace_ge _ home
  have rp:0 ≤ r:=by linarith only [φ.markG,abs_nonneg y,rA]
  have vp:0 ≤ v:=by linarith only [abs_nonneg y,vC]
  have ap:=wealth (e:=e) A X (u+a+ai) r DA ampA.1
  have bp:=wealth (e:=e) B Y (u+a+ai) r D_B ampB.1
  have ep:=wealth (e:=e) F Z (u+a) v DF ampE.1
  have pricePos:0 ≤ price:=by dsimp only [price,tariff];positivity
  have amount:0 ≤ (T^target)⁻¹*price:=by positivity
  apply WilsonSeparatedPrefixMovingNextCalendar.original R C older m (N-m) born om _ amount
  intro d hd f hf ordered
  let i:=m+d
  let j:=m+f
  have inside:j < N:=by have v:=mem_range.mp hf;dsimp only [j];omega
  have inear:i < N:=by dsimp only [i];omega
  have compares:m ≤ i:=Nat.le_add_right ..
  have jafter:m ≤ j:=Nat.le_add_right ..
  let x:=paceT R.draws.S m (i+1)
  let z:=paceT R.draws.S m (j+1)
  let ε:=epoch R older (j+1)
  have ep0:0 ≤ C.buy ε:=zero_le_one.trans (C.purchase (window R older m (j+1) born om (by omega)).1)
  have xx:0 < x:=pace_pos ..
  have zz:0 < z:=pace_pos ..
  have xp:x ≤ 1:=pace_le _ (by omega)
  have zp:paceT R.draws.S m j ≤ 1:=pace_le _ jafter
  have step:0 < paceT R.draws.S m i:=pace_pos ..
  have width:paceT R.draws.S m i ≤ 1:=pace_le _ compares
  change ‖nested R A B F φ ψ χ X Y Z o y t m older N q ω i j‖ ≤ (T^target)⁻¹*price*C.buy ε*(x*z^2)
  have nonneg:0 ≤ (T^target)⁻¹*price*C.buy ε*(x*z^2):=by positivity
  by_cases ordered':i < j
  · have head (miss:¬(VisitsT φ z y o).Nonempty ∨ ¬(VisitsT ψ z y o).Nonempty):
        cruises R.draws R.paid N (A.h+B.h) j (i+1)
          (JoinGap R.draws R.paid j N A.h B.h (current R A φ X m (j+1) N y o)
            (current R B ψ Y m (j+1) N y o))=0:=
      WilsonIndependentMatchedVacant.joined R (i+1) j N A.h B.h ordered' inside _ _
        (miss.imp (vacant R A φ X m (j+1) N y o) (vacant R B ψ Y m (j+1) N y o))
    have none (miss:¬(VisitsT χ (x/T) (y/T) o).Nonempty ∨
        ¬(VisitsT φ z y o).Nonempty ∨ ¬(VisitsT ψ z y o).Nonempty):
        nested R A B F φ ψ χ X Y Z o y t m older N q ω i j=0:=by
      have join:=WilsonIndependentMatchedVacant.joined R older i N F.h (A.h+B.h) (om.trans compares) inear
        (current R F χ Z t (i+1) N (y/T) o) _ (miss.imp (fun missed=>by
          have same:paceT R.draws.S t (i+1)=x/T:=by
            dsimp only [x,T,paceT];field_simp [(R.draws.S.a_pos m).ne',(R.draws.S.a_pos t).ne']
          apply vacant;simpa only [same] using missed) head)
      unfold nested;rw [if_pos ordered']
      exact congrArg (fun U:Era G ℝ=>U.2 q 0 ω) join
    by_cases av:(VisitsT φ z y o).Nonempty
    · by_cases bv:(VisitsT ψ z y o).Nonempty
      · by_cases fv:(VisitsT χ (x/T) (y/T) o).Nonempty
        · have ext:=WilsonSeparatedPrefixMovingLocator.separated χ T far y o farAway
          have roof:=WilsonSeparatedPrefixMovingLocator.paid (paceT R.draws.S m i) y o step.le width
          have floor:=WilsonSeparatedPrefixMovingLocator.site x y o xx
          have newCap:radiusH χ (paceT R.draws.S m i/T) (y/T) ≤ v:=
            cap χ (div_nonneg step.le tpos.le) (div_le_one_of_le₀ (width.trans tlarge) tpos.le) vE
          have bought:=fees R Po Pi Pd Pe PA PB PF older t m i j N born start home compares ordered' inside room
            φ ψ (WilsonSeparatedPrefixMovingLocator.booked y o) χ X Y Z o y near far r v DA D_B DF
            ampA ampB ampE nearPos farPos innerGap ext (cap φ (pace_pos ..).le zp rA)
            (cap ψ (pace_pos ..).le zp rB) (by rw [pace_step R.draws.S m i];exact roof.trans vC)
            (by rw [pace_step R.draws.S m i];exact newCap)
            av bv floor fv q hq ω
          have lower:x^extra ≤ x:=by
            simpa only [pow_one] using pow_le_pow_of_le_one xx.le xp (show 1 ≤ extra by dsimp only [extra];omega)
          change ‖nested R A B F φ ψ χ X Y Z o y t m older N q ω i j‖ ≤ _
          rw [nested,if_pos ordered']
          refine bought.trans ?_
          change ((T^target)⁻¹*(T^0)⁻¹*x^extra*z^2)*C.buy ε*price ≤ _
          simp only [pow_zero,inv_one,mul_one]
          calc
            _ ≤ (T^target)⁻¹*x*z^2*C.buy ε*price:=by gcongr
            _=_:=by ring
        · rw [none (Or.inl fv),norm_zero];exact nonneg
      · rw [none (Or.inr (Or.inr bv)),norm_zero];exact nonneg
    · rw [none (Or.inr (Or.inl av)),norm_zero];exact nonneg
  · rw [nested,if_neg ordered',norm_zero];exact nonneg

end YM.Integration.WilsonSeparatedPrefixMovingPairSector
