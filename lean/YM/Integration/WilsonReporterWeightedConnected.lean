import YM.Integration.WilsonReporterWeightedReturn

/-! Compact norm prices for the connected logarithm of the genuine original
held Wick reports. The age threshold is chosen before sites and regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedConnected
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West
open Set Filter Function RG Lattice Wilson Cells Marker Perch Atlas Ribbon Station Glyph Exponential
open scoped Topology BigOperators Classical ContDiff

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem exp_smooth : ContDiff ℂ 1 (@Poly.pass V _ (Stock.census V) _) := by
  have monomial (i : modes V) (k : ℕ) : ContDiff ℂ 1 (fun x : veil V => (x^k).part i) := by
    induction k generalizing i with
    | zero => simp only [pow_zero]; exact contDiff_const
    | succ k ih =>
      simp_rw [pow_succ, Glyph.part_mul]
      exact ContDiff.sum (fun j _ => (ih (scene j)).mul (Poly.get _).contDiff)
  change ContDiff ℂ 1 (fun x => (Poly.pass x).part)
  apply contDiff_pi.mpr
  intro i
  simp only [Poly.pass, Poly.part_sum, Poly.part_smul]
  exact ContDiff.sum (fun j _ => contDiff_const.mul (monomial i j))

private theorem log_smooth (k : ℕ) : ContDiff ℂ 1 (fun p : veil V => roll p k) := by
  induction k with
  | zero => exact contDiff_const
  | succ k ih => exact ih.add (contDiff_id.sub (exp_smooth.comp ih))

theorem book (B : ℝ) : ∀ᶠ s : ℝ in atTop, ∀ q p Q P : veil V, ‖p‖ ≤ B →
    Expands Q q → Expands P p → (∀ i, ‖q.part i-p.part i‖ ≤ bill (-63/64) s) →
    ‖Q-P‖ + bill (-3/2) s ≤ bill (-31/32) s := by
  let f := fun p : veil V => roll p (Fintype.card V)
  let K := Metric.closedBall (0 : veil V) (B+1)
  have sm : ContDiff ℝ 1 f := (log_smooth (V:=V) (Fintype.card V)).restrict_scalars ℝ
  obtain ⟨A,lip⟩ := (sm.contDiffOn (s:=K)).exists_lipschitzOnWith (by simp)
    (convex_closedBall ..) (isCompact_closedBall ..)
  filter_upwards [Glimmer.transports (show (-63:ℝ)/64 < -31/32 by norm_num) ((A:ℝ)+1)]
    with s rate q p Q P old hq hp packet
  have eps : 0 ≤ bill (-63/64) s := (Real.exp_pos _).le
  have one : bill (-63/64) s ≤ 1 := (Glimmer.billed s (show (-63:ℝ)/64≤0 by norm_num)).trans (Glimmer.bill_zero s).le
  have dq : ‖q-p‖ ≤ bill (-63/64) s := by
    change ‖q.part-p.part‖≤_
    exact (pi_norm_le_iff_of_nonneg eps).mpr packet
  have pm : p ∈ K := by
    change dist p 0 ≤ B+1
    rw [dist_zero_right]
    linarith
  have qm : q ∈ K := by
    change dist q 0 ≤ B+1
    rw [dist_zero_right]
    have qsum : ‖q‖≤‖q-p‖+‖p‖ := by simpa only [sub_add_cancel] using norm_add_le (q-p) p
    linarith only [old,dq,one,qsum]
  have logbound : ‖Q-P‖≤(A:ℝ)*bill (-63/64) s := by
    rw [show Q=f q from hq.uniq (rolls _ (hq.2 ▸ Poly.pass_part Q hq.1)),
        show P=f p from hp.uniq (rolls _ (hp.2 ▸ Poly.pass_part P hp.1))]
    exact (lip.norm_sub_le qm pm).trans (mul_le_mul_of_nonneg_left dq A.coe_nonneg)
  have spare := Glimmer.billed s (show (-3:ℝ)/2 ≤ -63/64 by norm_num)
  rw [add_mul,one_mul] at rate
  linarith only [rate,logbound,spare]

variable {G : Gauge} {C : Family G} {n : ℕ}
local notation "AX" => C.path.levels

theorem original (h : G.Simple) (B : ℝ) : ∀ᶠ k : ℕ in atTop,
    ∀ {N p : ℕ} {ξ : Purse} {P : (i : ℕ) → Rep G (C.side i p)} {x : Points n}
      {d : Fin n → ℕ} {Ψ : AtlasData G C.S p} (fit : FitSky AX ξ.band k x) (F : (i : Fin n) → StampDuty C k N p (d i) ξ.taylor (P k) ξ.era.coast.Q Ψ)
      (w v : (i : Fin n) → C.label (d i)),
    ‖Read.maxProfile C (tested AX ξ.band k x) (jointX w)‖ ≤ B →
    (∀ y : Chamber G C.S (middleSky AX ξ.band k) p → ℝ, Wind AX y (fraction n ξ.taylor (clim AX k)) →
      ∀ i : modes (Fin n), ‖(spunW (track Ψ) (fun j => prefaced (F j) (v j) (Station.choose AX ξ.band k x j))
        (beforeSky AX ξ.band k) y).part i - (Read.maxProfile C (tested AX ξ.band k x) (jointX w)).part i‖ ≤
        bill (-63/64) (clim AX k)) → WilsonReporterWeightedReturn.Signed w v fit F := by
  filter_upwards [(hat_rate AX h).eventually (book (V:=Fin n) B)] with k wage N p ξ P x d Ψ fit F w v bounded actual
  intro y hy
  exact wage _ _ _ _ bounded (expanders _ _ _ y) (Read.cumulative _ _ _ _) (actual y hy)

end YM.Integration.WilsonReporterWeightedConnected
