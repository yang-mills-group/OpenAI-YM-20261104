import YM.Integration.WilsonSeparatedPrefixMovingPinController
import YM.Integration.WilsonSeparatedPrefixMovingPairSector
import YM.Integration.WilsonSeparatedPrefixMovingUnformedCash
import YM.Integration.WilsonSeparatedPrefixMovingFineDeposit

/-! First contact of the actual distant column with the complete distinct
ordinary product, uniformly in the top and at every scalar grade. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingUnformedSector
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open Finset
open WilsonSeparatedPrefixMovingPinController (Sites collected still)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}

def fresh (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)(i:ℕ):ℝ:=
  let inner:=MassP G ℝ n (fun j=>current R (Q j) (φ j) (X j) m (i+1) N y o)
  let far:=current R F ψ Y t (i+1) N (y/paceT R.draws.S m t) o
  let h:=∑j,(Q j).h
  (cruises R.draws R.paid N (F.h+h) i older (JoinGap R.draws R.paid i N F.h h far inner)).2 q 0 ω

def mountedRow {u:ℕ}(R:Realm G (e+1) E)(canvas:Sites G e u)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)(i:ℕ):ℝ:=
  let inner:=MassP G ℝ n (fun j=>current R (Q j) (φ j) (X j) m (i+1) N y o)
  let far:=current R F ψ Y t (i+1) N (y/paceT R.draws.S m t) o
  let h:=∑j,(Q j).h
  (collected R canvas (F.h+h) N i older (JoinGap R.draws R.paid i N F.h h far inner)).2 q 0 ω

def invoice (Q:Fin (n+1)→SealR G)(F:SealR G)(X:Herit Q)(Y:F.Rider)(e k u a:ℕ)(r g DF:ℝ)(B:Fin (n+1)→ℝ):ℝ:=
  ((16*r)^u*(g⁻¹)^a)*(WilsonSeparatedPrefixMovingWages.coupon F Y e (u+a) r DF)*
    ((coinMat k e)^n*∏j,WilsonSeparatedPrefixMovingWages.coupon (Q j) (X j) e (u+a) r (B j))

private lemma wage (Q:SealR G)(X:Q.Rider)(e u:ℕ)(r b:ℝ)(h:0 ≤ b):
    0 ≤ WilsonSeparatedPrefixMovingWages.coupon Q X e u r b:=by
  have p:0 ≤ WilsonSeparatedPrefixMovingOwnDate.fee Q e X:=by unfold WilsonSeparatedPrefixMovingOwnDate.fee;positivity
  unfold WilsonSeparatedPrefixMovingWages.coupon;positivity

private lemma cap {d:ℕ}(φ:Rarity d){x y r:ℝ}(positive:0 ≤ x)(small:x ≤ 1)(roof:φ.radius+|y|+1 ≤ r):
    radiusH φ x y ≤ r:=by unfold radiusH;rw [abs_of_nonneg positive];linarith only [small,roof]

theorem mounted (H:Hol G)(Q:Fin (n+1)→SealR G)(F:SealR G)(k e u target:ℕ)(E W V Wo:Credit):
    let h:=∑j,(Q j).h
    let extra:=u+target+2
    let a:=h+F.h+extra
    ∃C:Credit,∀(R:Realm G (e+1) E)(canvas:Sites G e u)(_P:SpringD R k u a W)(_end:Dormitory R (F.h+h) u Wo)
      (_Q:HorizonP H R W V Q)(_F:PassportC H R F W V)
      (older t m N:ℕ)(_gate:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ m)(_top:m ≤ N)
      (_room:F.h+h ≤ k)(φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)(y g r DF:ℝ)
      (B:Fin (n+1)→ℝ),let T:=paceT R.draws.S m t
      let bill:=invoice Q F X Y e k u a r g DF B
      0 < g → (∀v,Amplitude (φ v) (B v)) → Amplitude ψ DF →
      (∀v,∀p∈tsupport (φ v).ψ.val,∀q∈tsupport ψ.ψ.val,T*g ≤ dist p (T • q)) →
      (∀v,(φ v).radius+|y|+1 ≤ r) → ψ.radius+|y/T|+1 ≤ r →
      ∀q ≤ e,∀ω:Fin 0→YForest G,‖∑d∈range (N-m),mountedRow R canvas Q F φ ψ X Y o y t m older N q ω (m+d)‖ ≤ 2*((T^target)⁻¹*bill)*C.buy (epoch R older m):=by
  intro h extra a
  obtain ⟨finish,earn⟩:=WilsonSeparatedPrefixMovingPinController.earlier G (F.h+h) e u E Wo
  let ledger:=WilsonSeparatedPrefixMovingUnformedCash.columns (n+1)
    (fun j=>WilsonSeparatedPrefixMovingWages.label H (Q j) e (u+a) E W V)
  let C:=(((finish.prodC (WilsonSeparatedPrefixMovingWages.effort G e k u a E W)).prodC
    (WilsonSeparatedPrefixMovingWages.label H F e (u+a) E W V)).prodC ledger)
  refine ⟨C.finances 1 le_rfl,?_⟩
  intro R canvas P endAt roster far older t m N gate start home top room φ ψ X Y o y g r DF B T bill
    pos ampA ampF separate nearBox farBox q hq ω
  have t0:0 < T:=pace_pos ..
  have t1:1 ≤ T:=pace_ge _ home
  have fundF:=wage F Y e (u+a) r DF ampF.1
  have fundA (j):=wage (Q j) (X j) e (u+a) r (B j) (ampA j).1
  have rp:0 ≤ r:=by linarith only [(φ 0).markG,abs_nonneg y,nearBox 0]
  have co:0 ≤ coinMat k e:=coinMat_nn ..
  have entire:0 ≤ ∏v,WilsonSeparatedPrefixMovingWages.coupon (Q v) (X v) e (u+a) r (B v):=Finset.prod_nonneg fun v _=>fundA v
  have bp:0 ≤ bill:=by dsimp only [bill,invoice];positivity
  have amount:0 ≤ (T^target)⁻¹*bill:=by positivity
  apply WilsonSeparatedPrefixMovingUnformedCash.calendar R C older m (N-m) gate (start.trans home) _ amount
  intro d hd
  let i:=m+d
  let Z:=epoch R older (i+1)
  let x:=paceT R.draws.S m (i+1)
  have live:m ≤ i:=Nat.le_add_right ..
  have edge:i < N:=by dsimp only [i];omega
  have d0:0 < x:=pace_pos ..
  have d1:x ≤ 1:=pace_le _ (by omega)
  have m0:0 < paceT R.draws.S m i:=pace_pos ..
  have m1:paceT R.draws.S m i ≤ 1:=pace_le _ live
  have tree:=window R older m (i+1) gate (start.trans home) (by omega)
  have ok:1 ≤ Z:=tree.1
  have cp:0 ≤ C.buy Z:=zero_le_one.trans (C.purchase ok)
  have farDate:paceT R.draws.S t (i+1)=x/T:=by
    dsimp only [x,T,paceT];field_simp [(R.draws.S.a_pos m).ne',(R.draws.S.a_pos t).ne']
  let near v:=current R (Q v) (φ v) (X v) m (i+1) N y o
  let ext:=current R F ψ Y t (i+1) N (y/T) o
  let inner:=MassP G ℝ n near
  let delta:=JoinGap R.draws R.paid i N F.h h ext inner
  change ‖(collected R canvas (F.h+h) N i older delta).2 q 0 ω‖ ≤ (T^target)⁻¹*bill*C.buy Z*x^2
  have missed (miss:ext=0 ∨ inner=0):‖(collected R canvas (F.h+h) N i older delta).2 q 0 ω‖ ≤ (T^target)⁻¹*bill*C.buy Z*x^2:=by
    rw [show collected R canvas (F.h+h) N i older delta=0 from
      WilsonSeparatedPrefixMovingPinController.vacant R canvas older i N F.h h (by omega) edge ext inner miss]
    change ‖(0:ℝ)‖ ≤ _
    rw [norm_zero];positivity
  by_cases all:∀v,(VisitsT (φ v) x y o).Nonempty
  · by_cases active:(VisitsT ψ (x/T) (y/T) o).Nonempty
    · let add:=h+2
      have same:a=u+F.h+target+add:=by dsimp only [a,extra,add];omega
      have trueAt:=WilsonSeparatedPrefixMovingFineDeposit.original R P Q F roster far i N t m
        (gate.trans start) home live edge target add extra rfl same room φ ψ X Y y g r Z B DF o
        tree.2.2.1 (window R older t (i+1) gate start (by omega)).2.2.1 pos ampA ampF separate
        (fun v=>by change radiusH (φ v) (paceT R.draws.S m (i+1)*(R.draws.S.block i).val) y ≤ r; rw [pace_step];exact cap _ m0.le m1 (nearBox v))
        (by change radiusH ψ (paceT R.draws.S m (i+1)*(R.draws.S.block i).val/T) (y/T) ≤ r;rw [pace_step];exact cap _ (div_nonneg m0.le t0.le) (div_le_one_of_le₀ (m1.trans t1) t0.le) farBox)
        all active
      let z:=R.cash (priceWG G e k u a E W) i
      let tariff:=(16*r)^u*(((ll R.draws i).L.val:ℝ)/g)^a
      let e₀:=unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a) F Y ψ Z (x/T) (y/T) DF
      let prices v:=unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a) (Q v) (X v) (φ v) Z x y (B v)
      have touched:=earn R canvas endAt older m i N gate (start.trans home) live edge.le delta trueAt.2.1 _
        (by rw [←pace_step R.draws.S m i];exact trueAt.2.2) q hq ω
      have received:‖(collected R canvas (F.h+h) N i older delta).2 q 0 ω‖ ≤ (T^target)⁻¹*(T^add)⁻¹*x^extra*(coinMat k e)^n*
            (finish.buy (epoch R older i)*(z*tariff)*e₀*∏v,prices v):=by
        refine touched.trans_eq ?_
        change finish.buy (epoch R older i)*(z*((((T^target)⁻¹*(T^add)⁻¹*x^extra)*tariff)*
          (e₀*((coinMat k e)^n*∏v,prices v))))=_;ring
      have close:=WilsonSeparatedPrefixMovingInvoice.credit R finish older i (i+1) gate (by omega) (by omega)
      have income:=WilsonSeparatedPrefixMovingInvoice.salary (W:=W) R older i (i+1) k u a gate (by omega) (by omega) r g rp pos
      have cE:=WilsonSeparatedPrefixMovingInvoice.desk (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) F Y ψ
        (u+a) Z (x/T) (y/T) r DF ok (cap ψ (div_nonneg d0.le t0.le) (div_le_one_of_le₀ (d1.trans t1) t0.le) farBox) ampF
      have input (v):=WilsonSeparatedPrefixMovingInvoice.desk (H:=H) (E:=E) (W:=W) (V:=V) (e:=e)
        (Q v) (X v) (φ v) (u+a) Z x y r (B v) ok (cap _ d0.le d1 (nearBox v)) (ampA v)
      have pack:=WilsonSeparatedPrefixMovingUnformedCash.bought (n:=n+1) _ _ _ input
      have paid:=(((close.mul income).mul cE).mul pack).grant
      have upper:(T^add)⁻¹ ≤ 1:=inv_le_one_of_one_le₀ (one_le_pow₀ t1)
      have mesh:x^extra ≤ x^2:=pow_le_pow_of_le_one d0.le d1 (by dsimp only [extra];omega)
      have external:0 ≤ (T^target)⁻¹:=by positivity
      have rates:((T^add)⁻¹*x^extra) ≤ x^2:=by
        exact (mul_le_mul_of_nonneg_right upper (pow_nonneg d0.le _)).trans ((one_mul _).le.trans mesh)
      have dues:finish.buy (epoch R older i)*(z*tariff)*e₀*∏v,prices v ≤ C.buy Z*((16*r)^u*(g⁻¹)^a*WilsonSeparatedPrefixMovingWages.coupon F Y e (u+a) r DF*
            ∏v,WilsonSeparatedPrefixMovingWages.coupon (Q v) (X v) e (u+a) r (B v)):=by
        simpa only [one_mul] using paid
      have allFees:0 ≤ finish.buy (epoch R older i)*(z*tariff)*e₀*∏v,prices v:=
        (((close.mul income).mul cE).mul pack).floor
      refine received.trans ?_
      calc
        _=((T^target)⁻¹*(coinMat k e)^n)*(((T^add)⁻¹*x^extra)*
              (finish.buy (epoch R older i)*(z*tariff)*e₀*∏v,prices v)):=by ring
        _ ≤ ((T^target)⁻¹*(coinMat k e)^n)*(x^2*(C.buy Z*((16*r)^u*(g⁻¹)^a*
            WilsonSeparatedPrefixMovingWages.coupon F Y e (u+a) r DF*
              ∏v,WilsonSeparatedPrefixMovingWages.coupon (Q v) (X v) e (u+a) r (B v)))):=
          mul_le_mul_of_nonneg_left (mul_le_mul rates dues allFees (sq_nonneg x)) (mul_nonneg external (pow_nonneg co _))
        _=_:=by dsimp only [bill,invoice];ring
    · apply missed (Or.inl ?_)
      apply WilsonSeparatedPrefixMovingPairSector.vacant;simpa only [farDate] using active
  · obtain ⟨v,bad⟩:=Classical.not_forall.mp all
    exact missed (Or.inr (GapZero near v (WilsonSeparatedPrefixMovingPairSector.vacant R (Q v)
      (φ v) (X v) m (i+1) N y o bad)))

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
      ∀q ≤ e,∀ω:Fin 0→YForest G,‖∑d∈range (N-m),fresh R Q F φ ψ X Y o y t m older N q ω (m+d)‖ ≤ 2*((T^target)⁻¹*bill)*C.buy (epoch R older m):=by

  intro h extra a
  obtain ⟨C,paid⟩:=mounted H Q F k e u target E W V Wo
  refine ⟨C,?_⟩
  intro R
  exact paid R (WilsonSeparatedPrefixMovingPinController.still G e u)

end YM.Integration.WilsonSeparatedPrefixMovingUnformedSector
