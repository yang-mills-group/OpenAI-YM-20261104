import YM.Integration.WilsonSeparatedPrefixMovingLateLaw
import YM.Integration.WilsonSeparatedPrefixMovingCapturedFees
import YM.Integration.WilsonSeparatedPrefixMovingLaterJoin
import YM.Integration.WilsonSeparatedPrefixMovingNearReturn
import YM.Integration.WilsonSeparatedPrefixMovingOwnDate

/-! A first join after capture. The near source includes the old scalar
and is the complete propagated difference on its own nominated chart.
The reflected exterior enters as its literal own-date normalized column. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingLateSector
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D a k k' e u extra:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {E W K U V V' L:Credit}

open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (birth near far)
open WilsonSeparatedPrefixMovingWages (coupon effort label lens)
open Finset
open scoped Classical

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(Q:SealR G)(a u extra k' e:ℕ)
    (v:Rails h k (u+a) e)(E W K U V V' L:Credit)(order:a=h+Q.h+extra):
    ∃C:Credit,∀(Y:CutsP H T p v E W K U),let R:=Y.vesselsC
      ∀(_far:PassportC H R Q W V')(_P:SpringD R k' u a V)(_old:Dormitory R (k+Q.h) u L)
      (older:ℕ)(_gate:R.anchor ≤ older)(_route:older ≤ Y.m)(_room:k+Q.h ≤ k')
      (φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y dist r Bφ Bψ:ℝ)(o:CellR),
      let Z:=epoch R older Y.ceilC
      let ratio:=paceT Y.ax.S Y.m Y.ceilC
      let bill:=(16*r)^u*(dist⁻¹)^a*((5*r)^4*(9^(u+a)*(Bφ*Y.fuel)))*coupon Q X e (u+a) r Bψ
      Amplitude φ Bφ → Amplitude ψ Bψ → ClearDay φ ψ dist → 0 < dist →
      φ.radius+|y|+1 ≤ r → ψ.radius+|y|+1 ≤ r →
      ∀q ≤ e,∀ω:Fin 0→YForest G,‖∑j∈range Y.i,(birth Y Q φ ψ X y o older j).2 q 0 ω‖ ≤ 
        Z*ratio^h*(bill*C.buy Z):=by
  obtain ⟨C₀,C₁,sale⟩:=WilsonSeparatedPrefixMovingLaterJoin.original H T p Q a u extra k' e v E W K U V V' L order
  let C:=((C₁.prodC (effort G e k' u a E V)).prodC C₀).prodC (label H Q e (u+a) E W V')
  refine ⟨C,?_⟩
  intro Y R outside P old older gate route room φ ψ X y dist r Bφ Bψ o Z ratio bill own outer separate positive
    nearBox farBox q hq ω
  have dawn:=window R older Y.m Y.ceilC gate route (Nat.le_add_right _ _)
  have warm:1 ≤ Z:=dawn.1
  have income:=WilsonSeparatedPrefixMovingCapturedFees.age Y older gate route
  have price:0 ≤ C.buy Z:=zero_le_one.trans (C.purchase warm)
  have rp:0 ≤ r:=by linarith only [φ.markG,nearBox,abs_nonneg y]
  have sup:0 ≤ bill:=by
    have b1:=own.1
    have b2:=outer.1
    have f:=Y.hf
    have hF:0 ≤ WilsonSeparatedPrefixMovingOwnDate.fee Q e X:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
    dsimp only [bill,coupon];positivity
  have rr:0 < ratio:=pace_pos ..
  have budget:0 ≤ ratio^h*(bill*C.buy Z):=by positivity
  have top:=Y.hc.trans Y.hn
  have one (j:ℕ)(born:j < Y.i):‖(birth Y Q φ ψ X y o older j).2 q 0 ω‖ ≤ ratio^h*(bill*C.buy Z):=by
    let i:=Y.m+j
    let x:=paceT Y.ax.S Y.m (i+1)
    let η:=paceT Y.ax.S Y.m i
    have ij:i ≤ Y.ceilC:=Nat.add_le_add_left born.le _
    have front:Y.m ≤ i:=Nat.le_add_right _ _
    have proper:i < Y.N:=lt_of_lt_of_le (Nat.add_lt_add_left born _) top
    have xp:0 < x:=pace_pos ..
    have x1:x ≤ 1:=pace_le Y.ax.S (by omega)
    have ep:0 < η:=pace_pos ..
    have e1:η ≤ 1:=pace_le Y.ax.S front
    have support {d:ℕ}(f:Rarity d)(s:ℝ)(sp:0 ≤ s)(small:s ≤ 1)(bound:f.radius+|y|+1 ≤ r):radiusH f s y ≤ r:=by
      unfold radiusH;rw [abs_of_nonneg sp];linarith
    let nearRow:=near Y φ y o (j+1)
    let farRow:=far Y Q ψ X y o (j+1)
    have miss (null:nearRow=0∨farRow=0):‖(birth Y Q φ ψ X y o older j).2 q 0 ω‖ ≤ ratio^h*(bill*C.buy Z):=by
      have gone:=WilsonIndependentMatchedVacant.joined R older i Y.N k Q.h (by omega) proper nearRow farRow null
      change ‖(cruises R.draws R.paid Y.N (k+Q.h) i older _).2 q 0 ω‖ ≤ _
      rw [gone];exact (norm_zero (E:=ℝ)).le.trans budget
    by_cases both:(VisitsT φ x y o).Nonempty
    · by_cases hit:(VisitsT ψ x y o).Nonempty
      · let scope:=lens Y.ax.S Y.m
        have sc:scope i= x*(ll R.draws i).L.val:=by
          change min 1 η=paceT Y.ax.S Y.m (i+1)*(Y.ax.S.block i).val
          rw [min_eq_right e1,pace_step]
        have current:Compar Y.ax.S R.y Y.m (i+1) ≤ Z:=
          (compar_age Y.ax.S R.y Y.m (Nat.add_le_add_left (show j+1 ≤ Y.i by omega) _)).trans dawn.2.2.1
        have clock:=window R older older i gate le_rfl (by omega)
        have fee:=sale Y outside P old j Y.m older born front room (epoch R older i) Z current
          Y.ha scope (WilsonSeparatedPrefixMovingWages.journey R older Y.m i gate (by omega)) clock.2.2.2
          φ ψ X y dist r Bφ Bψ o sc separate positive
          (by change radiusH φ (paceT Y.ax.S Y.m (i+1)*(Y.ax.S.block i).val) y ≤ r;rw [pace_step]
              exact support φ η ep.le e1 nearBox)
          (by change radiusH ψ (paceT Y.ax.S Y.m (i+1)*(Y.ax.S.block i).val) y ≤ r;rw [pace_step]
              exact support ψ η ep.le e1 farBox) both hit own outer
        have cc:=WilsonSeparatedPrefixMovingInvoice.credit R C₁ older i Y.ceilC gate (by omega) ij
        have scost:=WilsonSeparatedPrefixMovingInvoice.salary (e:=e) (W:=V) R older i Y.ceilC k' u a gate
          (by omega) ij r dist rp positive
        have nc:=WilsonSeparatedPrefixMovingCapturedFees.mount Y C₀ (j+1) (by omega) Z income φ (u+a) x y r Bφ
          (support φ x xp.le x1 nearBox) own
        have fc:=WilsonSeparatedPrefixMovingInvoice.desk (H:=H) (E:=E) (W:=W) (V:=V') (e:=e)
          Q X ψ (u+a) Z x y r Bψ warm (support ψ x xp.le x1 farBox) outer
        have earned:=((cc.mul scost).mul nc).mul fc
        let b:=u+a
        let nearFee:=(5*radiusH φ x y)^4*(9^b*(Bφ*WilsonIndependentMatchedCoverProfile.price Y C₀ (j+1) 1))
        let farFee:=(5*radiusH ψ x y)^4*(9^b*(Bψ*((polarBill H Q.ans Q.path e b E W V').choose.buy Z*
          WilsonSeparatedPrefixMovingOwnDate.fee Q e X)))
        let z:=R.cash (priceWG G e k' u a E V) i
        let spend:=(16*r)^u*(((ll R.draws i).L.val:ℝ)/dist)^a
        have paid: C₁.buy (epoch R older i)*(z*spend)*nearFee*farFee ≤ C.buy Z*bill:=by
          dsimp only [C,Z,bill,z,spend,nearFee,farFee,b]
          simpa only [one_mul,WilsonSeparatedPrefixMovingFineFare.unitFee] using earned.grant
        have nn:0 ≤ C₁.buy (epoch R older i)*(z*spend)*nearFee*farFee:=earned.floor
        have factor:x^extra ≤ 1:=pow_le_one₀ xp.le x1
        refine (fee.2.2 q hq ω).trans ?_
        calc
          _=ratio^h*(x^extra*(C₁.buy (epoch R older i)*(z*spend)*nearFee*farFee)):=by ring
          _ ≤ ratio^h*(C₁.buy (epoch R older i)*(z*spend)*nearFee*farFee):=
            mul_le_mul_of_nonneg_left (mul_le_of_le_one_left nn factor) (pow_nonneg rr.le _)
          _ ≤ _:=mul_le_mul_of_nonneg_left (paid.trans_eq (mul_comm ..)) (pow_nonneg rr.le _)
      · exact miss (Or.inr (WilsonSeparatedPrefixMovingPairSector.vacant R Q ψ X Y.m (i+1) Y.N y o hit))
    · exact miss (Or.inl (WilsonIndependentMatchedVacant.absent _ φ x y o h xp both))
  have days:=WilsonSeparatedPrefixMovingCalendar.days Y.ax.S Y.m Y.ceilC (Nat.le_add_right _ _)
  have start:=R.depth older gate
  have drift:=scales Y.ax.S route
  have span:(Y.i:ℝ) ≤ Z:=by
    change R.y older+2*(Y.ax.S.scale Y.ceilC-Y.ax.S.scale older)≥(Y.i:ℝ)
    simp only [CutsP.ceilC,Nat.add_sub_cancel_left] at days
    linarith only [days,start,drift]
  calc
    _ ≤ ∑j∈range Y.i,‖(birth Y Q φ ψ X y o older j).2 q 0 ω‖:=norm_sum_le ..
    _ ≤ ∑_j∈range Y.i,ratio^h*(bill*C.buy Z):=sum_le_sum fun j hj=>one j (mem_range.mp hj)
    _=(Y.i:ℝ)*(ratio^h*(bill*C.buy Z)):=by simp
    _ ≤ Z*(ratio^h*(bill*C.buy Z)):=mul_le_mul_of_nonneg_right span budget
    _=_:=by ring

end YM.Integration.WilsonSeparatedPrefixMovingLateSector
