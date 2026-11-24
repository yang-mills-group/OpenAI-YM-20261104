import YM.Integration.WilsonIndependentMatchedOwnHomeCoordinates
import YM.Integration.WilsonIndependentMatchedFreshPriceBook
import YM.Integration.WilsonIndependentFittedReportedWage
import YM.Integration.WilsonIndependentSpoutMasterCoordinates
import YM.Integration.WilsonSeparatedPrefixMovingOwnDate

/-! Price every actual own-date basis input on the elected Theatre.  The
forward engineering factor is the field height at all thermal orders. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeAxisWage
open Next.Foundations XSpace PertExtension WilsonCoeffUV.Wheel.Flooring
open Function Filter Finset Matrix Lattice RG Wilson Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonIndependentFittedForwardLength (factor)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{e:ℕ}{E W V A:Credit}

theorem matrix (H:Hol G)(Q:SealR G)(e:ℕ)(E W V:Credit):
    ∃C:Credit,∀S:CourseS H Q.ans Q.path e E W V,∀j ≤ e,∀a b:Alma Q.F,
      ‖lineS (CurNames S.vols.draws S.vols.paid Q.ans Q.path S.I.n S.spur S.length false) j a b‖ ≤
        factor S*C.buy S.Age:=by
  let Z (j:ℕ)(C:Credit):Prop:=∀S:CourseS H Q.ans Q.path e E W V,∀a b:Alma Q.F,
    ‖lineS (CurNames S.vols.draws S.vols.paid Q.ans Q.path S.I.n S.spur S.length false) j a b‖ ≤ factor S*C.buy S.Age
  have earned:∀j∈Finset.range (e+1),∃C:Credit,Z j C:=by
    intro j hj
    obtain ⟨C,paid⟩:=WilsonIndependentFittedForwardLength.original H Q.ans Q.path e E W V false j
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    exact ⟨C,fun S a b=>(paid S a b).main⟩
  obtain ⟨C,paid⟩:=uniformPays (P:=Z) (Finset.range (e+1)) earned
    (fun j _ _ _ le bill S a b=>(bill S a b).trans (mul_le_mul_of_nonneg_left (le _ S.I.warm) (WilsonIndependentFittedForwardLength.positive S).le))
  exact ⟨C,fun S j hj=>paid j (Finset.mem_range.mpr (by omega)) S⟩

theorem coefficients (L:Levels G)(O:ChartRatio G)(Q:SealR G)(N t m j:ℕ)(a b:Alma Q.F):
    PowerSeries.coeff j (street L O Q.ans Q.path N t (m-t) (PermuteLens L O Q N m (axis Q a)) b)=
      ∑z:Alma Q.F,lineS (CurNames L O Q.ans Q.path N t (m-t) false) j b z*
        (Wray L O Q.ans Q.path N m)⁻¹ z a:=by
  unfold street Matrix.mulVec dotProduct
  simp only [music,WilsonIndependentSpoutMasterCoordinates.inverse,reel_C,map_sum,
    PowerSeries.coeff_mul_C]
  rfl

theorem original (H:Hol G)(Q:SealR G)(e:ℕ)(E W V A:Credit):
    ∃C B:Credit,∀(R:Realm G (e+1) E)(_P:AheadT H R W V Q A)(t m N:ℕ),R.anchor ≤ t → t ≤ m → m ≤ N →
    ∀a:Alma Q.F,fee Q e (PermuteLens R.draws R.paid Q N t (brought R.draws R.paid Q N t m (axis Q a))) ≤
      (Fintype.card (Alma Q.F):ℝ)^2*(e+1)*(paceT R.draws.S m t)^Q.h*
      C.buy (Compar R.draws.S R.y t m)*B.buy (R.y m):=by
  obtain ⟨C,money⟩:=matrix H Q e E W V
  obtain ⟨B,wick⟩:=belt (H:=H) (C:=A) (T:=Q.ans) (p:=Q.path) (e:=e) (E:=E) (W:=W)
  refine ⟨C,B,?_⟩
  intro R P t m N start span live a
  let S:CourseS H Q.ans Q.path e E W V:=
    ⟨P.p.f,⟨P.p.f.arch.V,t,m-t,N,N,N,P.p.tap.trans_le start,by omega,le_rfl,le_rfl⟩,rfl⟩
  have date:t+(m-t)=m:=Nat.add_sub_of_le span
  have age:S.Age=Compar R.draws.S R.y t m:=by
    change P.p.f.arch.V.y t+(P.p.f.arch.V.draws.S.scale (t+(m-t))-_)+_=_
    rw [date,P.p.depths,P.p.lands];rfl
  have ratio:factor S=(paceT R.draws.S m t)^Q.h:=by
    change (Real.exp (P.p.f.arch.V.draws.S.scale (t+(m-t))-_))^_=_
    rw [date,P.p.lands,pace_rep]
    ring_nf
    rfl
  let price:=(paceT R.draws.S m t)^Q.h*C.buy (Compar R.draws.S R.y t m)
  let chalk:=B.buy (R.y m)
  have minFee:0 ≤ chalk:=zero_le_one.trans (B.purchase (R.depth _ (start.trans span)))
  have bank (b c:Alma Q.F):‖(Wray R.draws R.paid Q.ans Q.path N m)⁻¹ b c‖ ≤ chalk:=by
    have rule:=(wick P.p.f.arch P.stamps m m N N (P.p.tap.trans_le (start.trans span)) le_rfl live live b c).main
    simpa only [chalk,Realm.cash,P.p.lands,P.p.modes,P.p.depths] using rule
  have transfer (j:ℕ)(depth:j ≤ e)(b c:Alma Q.F):‖lineS (CurNames R.draws R.paid Q.ans Q.path N t (m-t) false) j b c‖ ≤ price:=by
    have r:=money S j depth b c
    rw [ratio,age] at r
    change ‖lineS (CurNames P.p.f.arch.V.draws P.p.f.arch.V.paid Q.ans Q.path N t (m-t) false) j b c‖ ≤ _ at r
    simpa only [price,P.p.lands,P.p.modes] using r
  have own:PermuteLens R.draws R.paid Q N t (brought R.draws R.paid Q N t m (axis Q a))=
      street R.draws R.paid Q.ans Q.path N t (m-t) (PermuteLens R.draws R.paid Q N m (axis Q a)):=by
    rw [←P.p.lands,←P.p.modes]
    exact (WilsonPositionProgramTrialFittedLens.original H Q P.p.f.arch (P.p.tap.trans_le start) span live _).1
  rw [own]
  unfold fee
  calc
    _ ≤ ∑_b:Alma Q.F,∑_j:Fin (e+1),∑_z:Alma Q.F,price*chalk:=by
      apply Finset.sum_le_sum;intro b _
      apply Finset.sum_le_sum;intro j _
      rw [coefficients];apply (norm_sum_le ..).trans
      apply Finset.sum_le_sum;intro z _
      rw [norm_mul]
      exact mul_le_mul (transfer _ (Nat.le_of_lt_succ j.isLt) b z) (bank z a) (norm_nonneg _) ((norm_nonneg _).trans (transfer _ (Nat.le_of_lt_succ j.isLt) b z))
    _ = _:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,price,chalk];ring

end YM.Integration.WilsonIndependentMatchedOwnHomeAxisWage
end
