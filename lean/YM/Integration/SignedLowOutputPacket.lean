import YM.Integration.SignedTreeOperator
import YM.Integration.SignedUniformReadout
import YM.Integration.OPEMSReport

/-! At every output horizon below four the entire running Reader packet
has the independently computed named MS tree limit, uniformly over
compact separated configurations and arbitrary independent input fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedLowOutputPacket
open Function Filter Set Spec OPE OPE.Orbits PhysMS Trace.Pilot FVA2 Pert.Position
open RG11.Fields RG11.Grove RG11.Neighborhood PhysicalMSOPECandidate SignedTreeOperator
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {n i D : ℕ} (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hG : G.Simple) (X : Climb.Scaling S)

include hG X in
theorem packet_scalar {I : Type} [Fintype I] {d : I → ℕ} (hD : D < 4)
    (x : I → E4) (o : E4) (v : Labels S d) :
    R.packet D x v o = Short.scalar F R x (Orbits.tags v) o • S.unit D := by
  unfold Reader.packet
  rw [Finset.sum_eq_single (0 : Fin (D+1))]
  · change F.sector.derivatives.rise (Nat.zero_le D) (R.fresh 0 x o v) = _
    have hs : Short.scalar F R x (Orbits.tags v) o • S.unit 0 = R.fresh 0 x o v :=
      Short.scalarizes F R X hG x (Orbits.tags v) o
    rw [← hs, map_smul,
      F.sector.derivatives.fixs R.lifts F.room.kernel.laws (Nat.zero_le D)]
  · intro j _ hj
    have hp : 0 < j.val := Nat.pos_of_ne_zero (fun he => hj (Fin.ext he))
    rw [Short.low_annihilator F R X hG hp ((Nat.le_of_lt_succ j.isLt).trans_lt hD)
      (R.fresh j.val x o v) (R.fresh_mem j.val x o v), map_zero]
  · simp

include hJ hG X in
theorem actual_scalar (hD : D < 4) :
    ∀ᶠ r in trail, ∀ (v : Fin n → E C.labels i) (x : Fin n → E4),
    actualOutput (D := D) F R J v r x =
      Short.scalar F R x (Orbits.tags (Frame.born J r v)) 0 • (Climb.Bel C.book).unit D := by
  filter_upwards [hJ.unit D] with r hr v x
  rw [actualOutput,packet_scalar F R hG X hD,map_smul,← hr,LinearEquiv.symm_apply_apply]

variable (hR : Foundation F R) (hV : ∀ k, Bid.pop (C.localSection k))
    {q : MS.Land.Booked (FVA2.ColorCode.wings G)} (M : MS.Land.MS_Data G q) (μ : ℝ)

include hJ hG X hR in
theorem compact (hD : D < 4) (v : Fin n → E C.labels i) (K : Set (Points n))
    (hK : IsCompact K) (hsep : K ⊆ conf n) :
    TendstoUniformlyOn (fun r z => actualOutput (D := D) F R J v r (r • z).ofLp)
      (fun z => Fountain.phys (Atoll.share C F.room.cutoff hV) M μ 0 z i v • (Climb.Bel C.book).unit D)
      trail K := by
  let L := ContinuousLinearMap.toSpanSingleton ℂ ((Climb.Bel C.book).unit D)
  have hs := OPEMSReport.physical_scalar_leading (M := M) (μ := μ) (F := F) (J := J)
    (H := hJ) (hC := F.room.cutoff) (hV := hV) (R := R) (hR := hR) (hG := hG) (X := X) v K hK hsep
  have ht := L.uniformContinuous.comp_tendstoUniformlyOn hs
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε, actual_scalar F R J hJ hG X hD]
    with r hr hu z hz
  rw [hu v _]
  exact hr z hz

include hJ hG X hR in
theorem independent (hD : D < 4) (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in trail, ∀ z ∈ K, ∀ v : Fin n → E C.labels i,
    ‖actualOutput (D := D) F R J v r (r • z).ofLp -
      Fountain.phys (Atoll.share C F.room.cutoff hV) M μ 0 z i v • (Climb.Bel C.book).unit D‖ ≤
        ε * ∏ j, ‖v j‖ := by
  let b := (tower C.labels i).b
  let c := cost (I := Fin n) b
  let V := Atoll.share C F.room.cutoff hV
  let target (z : Points n) : MultilinearMap ℂ (fun _ : Fin n => E C.labels i) (E C.labels D) :=
    (ContinuousLinearMap.toSpanSingleton ℂ ((Climb.Bel C.book).unit D)).toLinearMap.compMultilinearMap
      (Fountain.phys V M μ 0 z i)
  let D₀ (r : ℝ) (z : Points n) :=
    SignedUniformReadout.actualTensor (D := D) (i := i) F R J r (r • z).ofLp - target z
  have reads (r : ℝ) (z : Points n) (v : Fin n → E C.labels i) : D₀ r z v =
    actualOutput (D := D) F R J v r (r • z).ofLp - Fountain.phys V M μ 0 z i v • (Climb.Bel C.book).unit D := by
    change SignedUniformReadout.actualTensor F R J r (r • z).ofLp v - _ = _
    rw [SignedUniformReadout.actualTensor_apply]
    rfl
  have hc : 0 ≤ c := cost_nonneg _
  let η := ε/(c+1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hpay : c*η ≤ ε := by
    calc
      _ ≤ (c+1)*η := mul_le_mul_of_nonneg_right (by linarith) hη.le
      _ = _ := by dsimp only [η]; field_simp
  have hh (u : sheaf C.labels n i) : ∀ᶠ r in trail, ∀ z ∈ K, ‖D₀ r z (b ∘ u)‖ ≤ η := by
    have hm := compact F R J hJ hG X hR hV M μ hD (b ∘ u) K hK hsep
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hm η hη] with r hr z hz
    rw [reads]
    rw [norm_sub_rev]
    exact le_of_lt (by simpa only [dist_eq_norm] using hr z hz)
  filter_upwards [eventually_all.mpr hh] with r hr z hz v
  rw [← reads]
  exact (test_bound b (D₀ r z) v hη.le (fun u => Or.inr (hr u z hz))).trans
    (mul_le_mul_of_nonneg_right hpay (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end YM.Integration.SignedLowOutputPacket
