import YM.IterationFour.Vacuum.Financed
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum.Financed
open Lattice Wilson RG Function MeasureTheory Filter Currency Render Spending
open AnalyticBridge VerifiedReset Mint
open scoped Topology BigOperators ContDiff
open Address
variable {G : Gauge} {C : Family G} {r : ℕ} {D : Set ℕ} {Y : Purse} {ν : ℝ} {v : ℕ} {hg : G.Simple}
    {P : (N q : ℕ)→Plan C N q r} {t : ℕ→ℕ→ℕ→Pocket} (h : Booking t hg D Y P ν v)

-- include fine neighbor hats/prices at most the coarse .limit
lemma alloy (a : Levels G) (hg : G.Simple) (Y : Purse) (D : Set ℕ):
    fare a D (fun i=> Y.limit a (i.level+1)) Y.sigma ∧
      fare a D (fun i=> Y.guardBill a (i.level+1)) Y.w:= by
  constructor
  · apply Account.absoluteEdge hg (warm _)
    exact ⟨Y.fare,Y.cash,Eventually.of_forall fun i=> by rw [abs_of_pos (Y.limit_pos ..)]; exact Y.spends hg (Nat.le_succ i.level)⟩
  apply Account.relax (Account.onEdge a level (tenor D) Y.w)
  refine Eventually.of_forall fun i=> ?_
  rw [abs_of_pos (Y.guard_pos ..)]
  exact (across a hg (Y.above.trans Y.ahead) (Nat.le_succ i.level)).trans (le_abs_self _)

include h
lemma metals : fare C.path.levels D (fun i=> shiftBill ((P i.top i.period).layers i.level) (B C.path.levels i.level)*B C.path.levels i.level) 3 := by
  let a:=C.path.levels
  obtain ⟨K,hK,hP⟩:= rank_bill (G:=G) r v
  have he : Account a level (tenor D) (fun i=> K*unitBill ((P i.top i.period).layers i.level) (B C.path.levels i.level)) 3 :=by simpa using! ((Account.constant hg (warm _) a K).product h.first)
  refine Account.relax he ?_
  filter_upwards [h.printed,bright D] with i hi hv
  have hp:= WardBin.hot a i.level
  rw [abs_of_nonneg (mul_nonneg (shift_nn _ hi.1 hp) hp.le)]
  have hT:= (P i.top i.period).orders _ hv.2
  exact (hP _ (C.path.levels.budget i.level) _ hp (fun w hw=>⟨(hT w hw).2,hi.2 w hw⟩) hi.1).trans (le_abs_self _)

lemma sunshine (he : 11/5 < Y.sigma) (hn : Y.sigma<ν) (hv : Y.sigma< Y.w) : ∀ᶠ i in tenor D,
    let a:= C.path.levels; let m:= i.level; let N:=i.top; let q:= i.period
    let x:= fees t i
    Duty a m ((P N q).alpha m) (x.due (Y.limit a (m+1)) (Y.guardBill a (m+1))) x.forceEarly x.forceGoal:=by
  let a:=C.path.levels
  let X i := fees t i
  let M:= Address.level
  let Y0 i:= Y.limit a (M i+1); let W0 i := Y.guardBill a (M i+1)
  let s i:= (X i).due (Y0 i) (W0 i)
  let α (i:Address):=(P i.top i.period).alpha i.level
  let H i:= Time.softCeiling G (a.params (M i)) (|α i|)
  have hh:= soft_rate hg a h.slow (warm D) h.reset_alpha
  obtain ⟨hu,hμ⟩:= alloy a hg Y D
  have hμ': fare a D (fun i=> (X i).response * W0 i) Y.w:=by simpa only [zero_add] using! h.older.product hμ
  have hx:a= C.path.levels:=rfl
  have hpre : fare a D (fun i=> (X i).repeatCost) 0 := by
    refine Account.relax (Account.constant hg (warm _) a Y.theta) (h.gains.mono fun i hi=>?_)
    have hl:= (X i).prices_pos.1
    have hv: 1 ≤ 2+adjusting a (M i):= by linarith only [(show 0≤adjusting a (M i) from (Time.base_nonneg G _).1)]
    rw [abs_of_nonneg hl, abs_of_pos Y.pos]; exact (le_mul_of_one_le_left hl hv).trans hi
  have hs : fare a D s Y.sigma := by
    have hvX : fare a D (fun i=> (X i).repeatCost*Y0 i) Y.sigma:=by simpa only [zero_add] using! hpre.product hu
    exact (hvX.joint hg (warm _) (h.funds.lower hn.le)).joint hg (warm _) (hμ'.lower hv.le)
  let p i:= a.budget (M i)
  let c i:= H i*(1+((p i).B:ℝ))^ (4:ℕ)*(p i).threshold
  have hb: Account a M (tenor D) (fun i=> ((p i).B:ℝ)) 0:= Account.gathered M (warm _) (cover a hg)
  have hcc : Account a M (tenor D) c 1:= by
     have ht: Account a M (tenor D) (fun i=>H i*(1+((p i).B:ℝ))^(4:ℕ)) 0:=by
        have hC:Account a M (tenor D) H 0:=hh
        have hv := ((Account.constant hg (warm D) a 1).joint hg (warm _) hb).repeatOrder hg (warm _) 4
        simpa using! hC.product hv
     have he': Account a M (tenor D) (fun i=> (p i).threshold) 1:= Account.gathered M (warm _) (thermal a hg)
     simpa only [zero_add] using! ht.product he'
  let f i:=(X i).forceEarly/(X i).forceGoal
  let b (i:Address):ℝ:= ((p i).B+(p i).B+1:ℕ)^4*(f i+2*c i)
  have hh': Account a M (tenor D) b 1:= by
    have hx: Account a M (tenor D) (fun i=> ((p i).B+(p i).B+1:ℕ)^4*(1:ℝ)) 0:=by
      simp_rw [mul_one,Nat.cast_add]; simpa using! (((hb.joint hg (warm _) hb).joint hg (warm _) (Account.constant hg (warm _) a 1)).repeatOrder hg (warm _) 4)
    simp_rw [mul_one] at hx
    have hv : Account a M (tenor D) (fun i=>f i+2*c i) 1:= by
      refine h.masks.joint hg (warm D) ?_
      simpa using! ((Account.constant hg (warm D) a 2).product hcc)
    simpa only [zero_add] using! hx.product hv
  filter_upwards [hh'.vanishing hg (warm _) zero_lt_one (1/4) (by norm_num), h.entries,h.demand,
    hs 2 (by linarith only [he])] with i hi hγ hw hc
  have ht: s i ≤ (p i).threshold^2:= by
    have hk:= (le_abs_self (s i)).trans hc
    rw [Currency.weight_two] at hk
    exact hk.trans (Extension.UV.threshold_large ..)
  refine Mint.send a (M i) hγ hw.2 hw.1 ((Time.soft_table G (a.params (M i)) (p:=p i) ⟨rfl,rfl,rfl⟩
    (le_refl (|α i|)) ((X i).due_nn ((Y.limit_pos ..).le) ((Y.guard_pos ..).le)) ht)) ?_ ((le_abs_self (b i)).trans hi)
  exact mul_nonneg (mul_nonneg (Mint.soft_pos a (M i) _ (abs_nonneg _)) (by positivity)) (p i).threshold_pos.le

lemma charter (he : 11/5 < Y.sigma) (hn : Y.sigma<ν) (hv : Y.sigma< Y.w) (hC : C.Makes) :
    ∀ᶠ i in tenor D, Room C Y (P i.top i.period) i.level (fees t i) := by
  let a:=C.path.levels
  let x i:= fees t i
  let S(a:Address):= (P a.top a.period).layers a.level
  let Z (i:Address):=B a i.level
  let H i:= shiftBill (S i) (Z i); let Dg i:=(i:Address).level
  let T i:= H i * ((a.budget (Dg i)).threshold^2)⁻¹
  let A i:= adjusting a i
  have he':fare a D T 3 ∧ fare a D H 3 := by
    have he:= metals h
    constructor
    · refine Account.relax he ?_
      filter_upwards [h.printed] with i hi; have hq:= shift_nn (S i) hi.1 (WardBin.hot a i.level)
      change |H i * ((a.budget i.level).threshold ^ 2)⁻¹| ≤ _
      rw [abs_of_nonneg (mul_nonneg hq (inv_nonneg.mpr (sq_nonneg _)))]
      exact (mul_le_mul_of_nonneg_left (threshold_receipt a i.level) hq).trans (le_abs_self _)
    refine Account.relax he ?_
    filter_upwards [h.printed] with i hi; have hq:= shift_nn (S i) hi.1 (WardBin.hot a i.level)
    rw [abs_of_nonneg (show 0 ≤ H i from hq)]; exact (le_mul_of_one_le_right hq (a.fits.delayed i.level).le).trans (le_abs_self _)
  have hY : fare a D (fun i=>(x i).single+(x i).response*Y.guardBill a (Dg i+1)) (min Y.w ν) := by
    refine (h.funds.lower (min_le_right ..)).joint hg (warm _) ((show fare a D (fun i=> (fees t i).response*Y.guardBill C.path.levels (level i+1)) Y.w from ?_).lower (min_le_left ..))
    simpa only [zero_add] using! h.older.product (alloy a hg Y D|>.2)
  have hs: fare a D (fun i=> 1+ wall a i.level (S i)) 0 := by
    have hx:fare a D (fun i=> wall a i.level (S i)) 0:= Account.joint hg (warm _)
      (Account.gathered _ (warm _) h.slow.pre) (he'.1.lower (by norm_num: (0:ℝ)≤3))
    exact (Account.constant hg (warm D) a 1).joint hg (warm _) hx
  have hP : fare a D (fun i=> (1+wall a i.level (S i))*((x i).single+(x i).response*Y.guardBill a (Dg i+1))+
       H i*Y.guardBill a (Dg i)) (min Y.w ν):=by
    apply (show fare a D (fun i=> (1+wall a i.level (S i))*((x i).single+(x i).response*Y.guardBill a (Dg i+1))) (min Y.w ν) from zero_add (min Y.w ν) ▸ hs.product hY).joint hg (warm _)
    exact Account.lower (he'.2.product (Account.onEdge _ level _ Y.w)) ((min_le_left Y.w ν).trans (le_add_of_nonneg_left (by norm_num)))
  have hQ : fare a D (fun i=> Y.limit a i.level + unitBill (S i) (Z i)) (min Y.sigma 3):= by
    have ht : fare a D (fun i=> Y.limit a i.level) Y.sigma := by simpa only [zero_add] using! (Account.constant hg (warm D) a Y.fare).product (Account.onEdge a level _ Y.sigma)
    exact (ht.lower (min_le_left ..)).joint hg (warm _) (h.first.lower (min_le_right ..))
  filter_upwards [h.printed,validPrediction hg hC h.reset_terms, sunshine h he hn hv,
    h.demand,hQ _ (show (11:ℝ)/5 < min Y.sigma 3 from lt_min he (by norm_num)),hP.order hg (warm _) (lt_min hv hn)
    (mul_pos (sub_pos.mpr Y.fits) Y.cash),he'.1.vanishing hg (warm _) (by norm_num) 1 zero_lt_one,h.gains] with i hi hV hu hW ht hz h1 hL
  have hΩ:= renew_geo hg h.holo i.level
  refine ⟨hΩ.1,hΩ.2,hi.1,hV,(le_abs_self _).trans ht,hu,hW.2,?_,?_⟩
  · apply le_trans _ hL
    apply mul_le_mul_of_nonneg_right _ (x i|>.prices_pos.1)
    change 1+(A i.level+T i) ≤ 2+A i.level
    linarith only [h1,le_abs_self (T i)]
  exact (le_abs_self _).trans (hz.trans_eq (mul_assoc ..))

theorem funded (ht : C.Makes) {η : ℝ} (he : 0 < η ∧ η < 1/2) (hr : 2≤r)
    (hx : Y.sigma = r+1-η) (hv : Y.sigma < Y.w) (hν : Y.sigma<ν)
    (hl : ∀ᶠ i:ℕ in atTop,∀ N q, q∈D → i ≤ N → Counter (P N q) Y (t N q) i):
    ∀ᶠ m : ℕ in atTop,∀ N q, q∈D → m≤N → ∃ L,Obtains N q m Y r (P N q) (t N q) L := by
  apply charging hg ht hr he _ hx
  · exact ticket_income hg ht _ (by linarith only [he.1,hx]) h.reset_terms
  have hs: 11/5 < Y.sigma:= by
    have hk:(2:ℝ)≤r:= by exact_mod_cast hr
    linarith only [hk,he.2,hx]
  exact ⟨((pass_iff _ _).1 (charter h hs hν hv ht)).mono fun _ ha N q hi hh=>ha N q ⟨hi,hh⟩,hl⟩
end YM.IterationFour.Vacuum.Financed
