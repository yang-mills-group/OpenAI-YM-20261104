import YM.Integration.WilsonPositionProgramNominatedPublicScalar
import YM.Integration.WilsonPositionProgramNominatedMenuInvoice

/-! One previously purchased course hears arbitrary filed numerical axes with
uniform fixed-reporter income.  The original periods and internal UV tops are
independent, and the two programs always receive the same signed coordinates. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramMeteredPublicResponse
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Fountain
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Winding WilsonCoeffUV.Layout WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops WilsonPositionProgramThermometerCoordinates
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNominatedRoster (selected)
open WilsonPositionProgramNominatedWinding (output unitFare)
open scoped Topology BigOperators Classical
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Embroider.Canvas
open WilsonPositionProgramNominatedWinding (physical period age address active)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonMarkedIndependentMixedMomentTensor (Tensor)
variable {G:Gauge}(R:Run G){a D k u e:ℕ}
theorem reporter (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d fit) ≤ k):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1≤zz L m → ∀(money:Fin (a+1)→ℝ)(Z:ℝ)(B:Fin (a+1)→ℝ)(ε:ℝ),0<ε →
    ∃K:ℕ,m≤K ∧ ∀n:ℕ,K≤n → ∀X:Herit Q,(∀i,fee X e i ≤ money i) →
    ∀φ:Wilt Q,Compar L.S (zz L) m m≤Z → Bough Q φ 1 Z B →
    ∀t:ℕ,t≤e → ∀i:Alma ((primes G).F 0),
      let x:=normalized L R.metals.O Q X m
      let read:=fun n=>∫o:CellR,(locale o (LodeStar L R.metals.O φ (x n) m m n 1)).2 t 0 Fin.elim0 ∂dayMeasure
      let fixed:=PowerSeries.coeff t (lodgeIn L R.metals.O ((primes G).T 0) big φ x m m m k i)
      Tendsto read atTop (𝓝 fixed) ∧ ‖read n-fixed‖<ε:=by
  intro Q L
  obtain ⟨c,w,tariff⟩:=WilsonPositionProgramNormalizedMaster.original R simple v paid big rails l d fit cap
  filter_upwards [tariff] with m settled
  intro clock money Z B ε tol
  let F:=max 1 (c.buy Z*∏i,B i*(w.buy (zz L m)*money i))
  have limit:Tendsto (fun n=>F*trailC L.S m n) atTop (𝓝 0):=by
    simpa using (fade L.S m).const_mul F
  obtain ⟨n₀,stop⟩:=eventually_atTop.mp (limit (Iio_mem_nhds tol))
  let K:=max m n₀
  refine ⟨K,le_max_left ..,?_⟩
  intro n enough X budget φ room shape t grade i x read fixed
  have base:paceT L.S m m=1:=by exact div_self (L.S.a_pos m).ne'
  have shape':Bough Q φ (paceT L.S m m) Z B:=base ▸ shape
  have income:0≤w.buy (zz L m):=zero_le_one.trans (w.purchase clock)
  have gross:c.buy Z*∏i,B i*(w.buy (zz L m)*fee X e i)≤F:=by
    apply le_trans _ (le_max_right 1 _)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (c.purchase shape.pos))
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (shape.lanes i).1 (mul_nonneg income
        (Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _))
    · intro i _
      apply mul_le_mul_of_nonneg_left _ (shape.lanes i).1
      apply mul_le_mul_of_nonneg_left _ income
      exact budget i
  let row:=fun n=>PowerSeries.coeff t (Reports L R.metals.O ((primes G).T 0) big φ (x n) m m m n k i)
  have seen:=settled X m m le_rfl le_rfl φ B Z room shape' t grade i
  have eq:row=read:=funext fun n=>WilsonPositionProgramReportedCell.original L R.metals.O
    ((primes G).T 0) big φ (x n) m n k t i
  have paired:=seen.2 K n (le_max_left ..) enough
  rw [←eq]
  exact ⟨seen.1,paired.gap.trans_lt ((mul_le_mul_of_nonneg_right gross (trail_pos ..).le).trans_lt
    (stop K (le_max_right ..)))⟩


theorem winding (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)(δ:ℝ)
    (income:WilsonPositionProgramUniformWindingTable.Complete R l d fit e unitFare δ):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∀ᶠ b:ℕ in atTop,∀m:ℕ,b ≤ m → ∃s:ℝ,0<s ∧
    ∀(sources:ℕ→ℕ→Herit Q)(money:Fin (a+1)→ℝ),
    (∀N p, m<N → ∀i,fee (sources N p) e i ≤ money i) →
    ∀φ:Wilt Q,(∀i j,i≠j → ClearDay (φ i) (φ j) (δ*longLog L m+14)) →
    ∀D t r:ℕ,t≤e → ∀z:Fin r→YForest G,∃C:ℝ,0≤C ∧ ∀ᶠ p:ℕ in atTop,
    ∀N per n:ℕ,m<N → m≤n →
      let Y:=output R l d fit m b n D φ (sources N per)
      ‖Y.1 (R.family.side b p) t r (slideC (R.family.side b p) z)-Y.2 t r z‖≤C*catchW s (R.family.side b p):=by
  intro Q L
  obtain ⟨c,scale⟩:=eventually_atTop.mp (WilsonPositionProgramWindingSlotScale.original R simple v paid l d fit e)
  filter_upwards [income,eventually_ge_atTop c] with b issued cb
  intro m bm
  have scales:=scale m (cb.trans bm)
  obtain ⟨s,hs,hear⟩:=issued m bm
  refine ⟨s,hs,?_⟩
  intro sources money funded φ clear D t r ht z
  let w(i:Fin (a+1)):ℝ:=max 1 (money i)
  have wp(i):0<w i:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  let X(q:ℕ):Herit Q:=sources (physical m q) (period m q)
  let Y(q:ℕ):Herit Q:=onSlots Q (X q) (fun i=>(w i)⁻¹)
  have bound(q i):fee (X q) e i ≤ w i:=by
    exact (funded (physical m q) (period m q) ((Nat.lt_succ_self m).trans_le (le_max_left ..)) i).trans (le_max_right ..)
  have bill(q i):WilsonConditionalTaylorSeparatedPurchase.fee (Q i) (Y q i) e ≤ unitFare.buy (zz L m):=by
    simpa only [unitFare,Credit.buy,pow_zero,mul_one] using WilsonPositionProgramWindingSlotScale.residual Q (X q) w wp (bound q) i
  have low(q):m≤age m q:=le_max_left ..
  have funds:Tensor G (Vote D) m e (R.family.side b) (fun p=>catchW s (R.family.side b p))
      (fun q=>output R l d fit m b (age m q) D φ (Y q)):=
    (hear Y (age m) (fun q _=>low q) (fun q _=>bill q) φ clear).2 D
  let total:=∏i,w i
  obtain ⟨C,hC,priced⟩:=WilsonMarkedIndependentMixedMomentTensor.smul total funds t ht r z
  refine ⟨C,hC,?_⟩
  filter_upwards [priced] with p allq
  intro N per n mN mn bank
  let q:=address m N per n
  obtain ⟨top,rep,atn⟩:=active m N per n mN mn
  have valid:m≤q:=Nat.le_add_right ..
  have held:= (allq q valid).2.2
  let small:=output R l d fit m b (age m q) D φ (Y q)
  have same:bank=total • small:=by
    change output R l d fit m b n D φ _=_
    have auth:=scales b (age m q) D bm (low q) (X q) w φ wp
    change output R l d fit m b (age m q) D φ (X q)=total • small at auth
    rw [←auth]
    simp only [X,q,top,rep,atn]
  rw [same]
  exact held


theorem original (simple:G.Simple)(hR:RG05Preconstruction.ReadoutPurchase R.b)
    (paid:WilsonPositionProgramNominatedMenuInvoice.issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d fit) ≤ k){δ:ℝ}(pos:0<δ):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1≤zz L m →
    ∀(sources:ℕ→ℕ→Herit Q)(money:Fin (a+1)→ℝ),
    (∀N p,m<N → ∀i, fee (sources N p) e i ≤ money i) →
    ∀(Z:ℝ)(B:Fin (a+1)→ℝ)(ε:ℝ),0<ε →
    ∃K:ℕ,m≤K ∧ ∀φ:Wilt Q,Compar L.S (zz L) m m≤Z → Bough Q φ 1 Z B →
      (∀i j,i≠j → ClearDay (φ i) (φ j) (δ*longLog L m+14)) →
      ∀ᶠ p:ℕ in atTop,∀(N per n:ℕ),m<N → K≤n → ∀t:Fin (e+1),∀i:Alma ((primes G).F 0),
      let X:=sources N per
      let fixed:=PowerSeries.coeff t.val (lodgeIn L R.metals.O ((primes G).T 0) big φ
        (normalized L R.metals.O Q X m) m m m k i)
      ‖WilsonPositionProgramNominatedPublicScalar.finite R l d fit m n p t D φ X i-fixed‖<ε:=by
  intro Q L
  let v:ℕ→Gear G→ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  have invoice:=WilsonPositionProgramNominatedMenuInvoice.original R simple hR paid l d fit e unitFare pos
  filter_upwards [winding R simple v paid.1 l d fit δ invoice,reporter R simple v paid.1 big rails l d fit cap] with m finiteCover master
  obtain ⟨s,hs,hear⟩:=finiteCover m le_rfl
  intro clock sources money funded Z B ε tol
  have half:0<ε/2:=half_pos tol
  obtain ⟨K,mK,stopped⟩:=master clock money Z B (ε/2) half
  refine ⟨K,mK,?_⟩
  intro φ room shape clear
  let E:=(primes G).F 0
  have each (t:Fin (e+1))(i:Alma E):∀ᶠ p:ℕ in atTop,∀N per n:ℕ,m < N → K ≤ n →
      let X:=sources N per
      let fixed:=PowerSeries.coeff t.val (lodgeIn L R.metals.O ((primes G).T 0) big φ
        (normalized L R.metals.O Q X m) m m m k i)
      ‖WilsonPositionProgramNominatedPublicScalar.finite R l d fit m n p t D φ X i-fixed‖<ε:=by
    have ht:t.val≤e:=Nat.le_of_lt_succ t.isLt
    obtain ⟨C,_,sale⟩:=hear sources money funded φ clear D t 0 ht Fin.elim0
    let w:=brow E i D
    have decay:Tendsto (fun p=>C*‖w‖*catchW s (R.family.side m p)) atTop (𝓝 0):=by
      simpa using (WilsonMarkedIndependentMixedOrderedWinding.disappears R s hs (b:=m)).const_mul (C*‖w‖)
    filter_upwards [sale,decay (Iio_mem_nhds half)] with p sold small
    intro N per n late enough X fixed
    let Y:=output R l d fit m m n D φ X
    let finiteRead:=Y.1 (R.family.side m p) t.val 0 (slideC (R.family.side m p) Fin.elim0)
    let coverRead:=Y.2 t.val 0 Fin.elim0
    have difference:‖finiteRead w-coverRead w‖≤(C*‖w‖)*catchW s (R.family.side m p):=by
      calc
        ‖finiteRead w-coverRead w‖=‖(finiteRead-coverRead) w‖:=rfl
        _ ≤ ‖finiteRead-coverRead‖*‖w‖:=(finiteRead-coverRead).le_opNorm w
        _ ≤ (C*catchW s (R.family.side m p))*‖w‖:=mul_le_mul_of_nonneg_right
          (sold N per n late (mK.trans enough)) (norm_nonneg _)
        _ = _:=by ring
    have anchored:‖coverRead w-fixed‖<ε/2:=by
      have near:=(stopped n enough X (funded N per late) φ room shape t ht i).2
      have certificate:=WilsonPositionProgramReportedUnit.original L R.metals.O ((primes G).T 0)
        big φ (normalized L R.metals.O Q X m n) m n k t i
      have summed:=WilsonPositionProgramReportedCell.original L R.metals.O ((primes G).T 0)
        big φ (normalized L R.metals.O Q X m n) m n k t i
      exact (congrArg (fun x:ℝ=>‖x-fixed‖) (certificate.symm.trans summed)).trans_lt near
    calc
      ‖finiteRead w-fixed‖≤‖finiteRead w-coverRead w‖+‖coverRead w-fixed‖:=norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε :=by linarith [difference.trans_lt (show (C*‖w‖)*catchW s (R.family.side m p)<ε/2 from small)]
  filter_upwards [eventually_all.mpr (fun t=>eventually_all.mpr (each t))] with p received
  exact fun N per n h enough t i=>received t i N per n h enough


end YM.Integration.WilsonPositionProgramMeteredPublicResponse
end
