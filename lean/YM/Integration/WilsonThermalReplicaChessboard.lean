import YM.Integration.WilsonThermalReplicaPressure

/-! The original multi-test thermal chessboard on a stage-wise actual room. The
coarse functions and every full reference are lifted on the very same fine run. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.ReplicaChessboard
open Function Filter Set MeasureTheory Lattice Wilson RG Next.Rank Push.GridApprox Cells WardBin.Wheels
open scoped ENNReal Topology BigOperators Classical
variable {G:Gauge} {H:History G} {i k N p : ℕ}

/-- The functions may vary independently with the genuine cell index. -/
theorem lift_array (hi : i ≤ k) (hk : k ≤ N) (r:ℕ) (roomy : room H.levels i k r)
    (f : (tilesAt H.S p hi).Cell → Config G (H.S.side k p) → ℂ)
    (loc : ∀j,Interior (window 0 r) (f j)) :
    backTo H N p hk ((tilesAt H.S p hi).fullAt f) =
      (tilesAt H.S p (hi.trans hk)).fullAt (fun j => backTo H N p hk (f j)) := by
  let M:=tilesAt H.S p hi
  let a (j:M.Cell):=M.copy j (f j)
  have ht:=backTo_cells H N p hi hk Finset.univ a r
    (fun j _=>copy_window H p hi j r (f j) (loc j)) roomy
  apply ht.trans
  funext W
  apply Finset.prod_congr rfl
  exact fun j _=>congrFun (backTo_copy H N p hi hk j (cylinder_env (loc j))) W

theorem original (Y : H.Selected) (hi : i ≤ k) (hk : k ≤ N) (r:ℕ) (roomy : room H.levels i k r)
    (f : (tilesAt H.S p hi).Cell → Config G (H.S.side k p) → ℂ)
    (loc : ∀j,Interior (window 0 r) (f j)) (e : (tilesAt H.S p hi).Cell → ℝ) (cost : ∀j,0 ≤ e j)
    (full : ∀j,‖∫ U,(tilesAt H.S p hi).fullAt (fun _=>f j) U ∂scene H N p k‖ ≤
      (e j)^(Fintype.card (tilesAt H.S p hi).Cell)) :
    ‖∫ U,(tilesAt H.S p hi).fullAt f U ∂scene H N p k‖ ≤ ∏j,e j := by
  let M:=tilesAt H.S p hi
  let T:=tilesAt H.S p (hi.trans hk)
  let β:=H.β N p N
  let g (j:M.Cell):=backTo H N p hk (f j)
  have bd (j:M.Cell) : Interior (T.chamber 0) (g j):=by
    apply Interior.enlarges (backTo_local H N p hi hk 0 r (F:=f j) ?_) (room_fits p H.levels r hi hk roomy 0)
    rw [anchor,←Ratio.root_embed,map_zero];exact loc j
  have equal (u:M.Cell → Config G (H.S.side k p) → ℂ) (l : ∀j,Interior (window 0 r) (u j))
      (hU : ∀j,Interior (T.chamber 0) (backTo H N p hk (u j))) :
      (∫ W,M.fullAt u W ∂scene H N p k)=moment β (T.fullAt (fun j=>backTo H N p hk (u j))) := by
    have E : Envelope (M.fullAt u) := Envelope.prodC Finset.univ (fun j=>M.copy j (u j))
      (fun j _=>cylinder_env (copy_window H p hi j r (u j) (l j)))
    rw [←retro Y hk le_rfl (M.fullAt u) E,lift_array hi hk r roomy u l,
      onstage Y _ (T.manyIntegral β _ hU)]
  have law : Seam G (H.S.side N p) β := laws _ _ _ (by
    apply le_trans _ (Y.represents N p N le_rfl).band.1
    have h:=H.levels.fits.delayed N
    linarith only [h])
  have jp:=T.planted law id injective_id g bd
  have positive (j : M.Cell) : 0 ≤ T.rootTest β (g j) := Real.rpow_nonneg (norm_nonneg _) _
  have root (j : M.Cell) : T.rootTest β (g j) ≤ e j := by
    apply le_of_pow_le_pow_left₀ T.cells_positive.ne' (cost j)
    have hj := full j
    rw [equal (fun _ => f j) (fun _ => loc j) (fun _ => bd j)] at hj
    exact (T.powering β (g j)).trans_le hj
  rw [equal f loc bd]
  exact jp.trans (Finset.prod_le_prod (fun j _ => positive j) (fun j _ => root j))

/-- One original mesh prices every finite heterogeneous array. Any number of
its independently chosen entries can use the actual measured hot plaquette
instead of a separately submitted full-array estimate. -/
theorem purchased (P : Poetry H.levels) (hG : G.Simple) (Y : H.Selected) :
    ∀ᶠ k : ℕ in atTop, ∃ (i : ℕ) (hi : i ≤ k), room H.levels i k 2 ∧
      (∀ p : ℕ, ((H.S.toDepth hi p).count.val : ℝ) ≤ (sigmaU H.levels k) ^ 2) ∧
      ∀ N : ℕ, k ≤ N → ∀ (p : ℕ)
        (f : (tilesAt H.S p hi).Cell → Config G (H.S.side k p) → ℂ),
        (∀ j, Interior (window 0 2) (f j)) → ∀ e : (tilesAt H.S p hi).Cell → ℝ,
        (∀ j, 0 ≤ e j) → (∀ j,
          (∃ t : Face (Per (H.S.side k p)),
            (touched t : Set _) ⊆ (tilesAt H.S p hi).chamber 0 ∧
            f j = fires t (cool H.levels k) ∧
            Real.exp (-4 * (sigmaU H.levels k) ^ 11) ≤ e j) ∨
          ‖∫ U, (tilesAt H.S p hi).fullAt (fun _ => f j) U ∂scene H N p k‖ ≤
            (e j) ^ Fintype.card (tilesAt H.S p hi).Cell) →
          ‖∫ U, (tilesAt H.S p hi).fullAt f U ∂scene H N p k‖ ≤ ∏ j, e j := by
  filter_upwards [ReplicaPressure.purchased P hG Y] with k ⟨i, hi, hroom, hmesh, paid⟩
  refine ⟨i, hi, hroom, hmesh, ?_⟩
  intro N hk p f loc e he either
  apply original Y hi hk 2 hroom f loc e he
  intro j
  rcases either j with ⟨t, inside, eq, price⟩ | known
  · rw [eq]
    exact (paid N hk p t inside).trans (pow_le_pow_left₀ (Real.exp_pos _).le price _)
  exact known

end YM.OPE.Therm.ReplicaChessboard
end
