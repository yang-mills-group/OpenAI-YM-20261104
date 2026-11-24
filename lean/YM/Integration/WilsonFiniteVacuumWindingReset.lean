import YM.Integration.WilsonFiniteVacuumWindingDate

/-! Reissue the actual finite and cover quiet inputs after the common kinetic reset.
The same incoming positive-grade bill purchases every output grade and rank. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFiniteVacuumWindingReset
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G : Gauge} {e m : ℕ} {E : Credit}

/-- Take one spatial width and one polynomial rent before all deployments. -/
theorem common {T : Type} [Fintype T] [Nonempty T] (s C : T → ℝ) (d : T → ℕ)
    (hs : ∀ t, 0 < s t) (hC : ∀ t, 0 ≤ C t) :
    ∃ (σ B : ℝ) (D : ℕ), 0 < σ ∧ 1 ≤ B ∧ ∀ t, σ ≤ s t ∧
      ∀ V : ℝ, 1 ≤ V → C t*V^(d t) ≤ B*V^D := by
  classical
  let B := 1+∑ t, C t
  let D := ∑ t, d t
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun t _ => hC t)
  refine ⟨Finset.univ.inf' Finset.univ_nonempty s,B,D,?_,hB,?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun t _ => hs t
  intro t
  refine ⟨Finset.inf'_le _ (Finset.mem_univ t),?_⟩
  intro V hV
  have leB : C t ≤ B := (Finset.single_le_sum (fun b _ => hC b) (mem_univ t)).trans
    (le_add_of_nonneg_left zero_le_one)
  have leD : d t ≤ D := Finset.single_le_sum (fun b _ => Nat.zero_le _) (mem_univ t)
  exact mul_le_mul leB (pow_le_pow_right₀ hV leD) (pow_nonneg (zero_le_one.trans hV) _)
    (zero_le_one.trans hB)

/-- Uniform native bound for the actual reversion at a fixed date and finite order. -/
theorem rim (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) {a : ℕ} (ha : a ≤ e) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N, m < N → rimJ (ratioHigh Q.draws Q.paid N m) a r ≤ B := by
  obtain ⟨d,gates⟩ := rimMoney G a r e ha
  obtain ⟨C,hC,gate⟩ := gates (Q.mint m hm).gear
  let u := Q.cash (costXV G e E) m
  have hu := Credit.purchase (costXV G e E) (Q.depth m hm)
  refine ⟨C*u^d,mul_nonneg hC (pow_nonneg (zero_le_one.trans hu) _),?_⟩
  intro N cut
  exact gate (ReelTime Q (i:=e) le_rfl hm cut (le_refl N) (le_refl N))

/-- One before-cutoff loan covers every retained angular tensor of the actual and
the independently prescribed vacua after the very same cover kinetic reversion. -/
theorem original (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) {s : ℝ} (hs : 0 < s) :
    ∃ (D : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀ V : ℝ, 1 ≤ V →
      WilsonFiniteVacuumWindingDate.positive Q.draws Q.paid e N (m+1) s V →
      ∀ (n : Side) a, a ≤ e → ∀ l,
      Sight ((story Q.draws Q.paid N m).1 n a l) (actionW Q.draws Q.paid N m a l) σ (C*V^D) := by
  classical
  let T := Fin (e+1) × Fin (e+2)
  choose d C s' hc hs' price using fun t : T => WilsonFiniteVacuumWindingDate.prior
    (r:=t.2.val+1) Q hm (Nat.lt_succ_iff.mp t.1.isLt) hs
  obtain ⟨σ,B,D,hσ,hB,enough⟩ := common s' C d hs' hc
  choose cost hcost reset using fun t : T => rim Q hm (Nat.lt_succ_iff.mp t.1.isLt) (t.2.val+1)
  let H := 1+∑ t : T, cost t
  have hH : 1 ≤ H := le_add_of_nonneg_right (Finset.sum_nonneg fun t _ => hcost t)
  refine ⟨D,H*B,σ,one_le_mul_of_one_le_of_one_le hH hB,hσ,?_⟩
  intro N cut V hV paid n a ha l
  have b0 : 0 ≤ B*V^D := mul_nonneg (zero_le_one.trans hB) (pow_nonneg (zero_le_one.trans hV) _)
  have all0 : 0 ≤ H*B*V^D := mul_nonneg (mul_nonneg (zero_le_one.trans hH) (zero_le_one.trans hB))
    (pow_nonneg (zero_le_one.trans hV) _)
  cases l with
  | zero => exact (WilsonFiniteCommonKineticReset.quiet _ _ cut n a σ).more all0
  | succ r =>
    by_cases hr : r < e+2
    · let t : T := (⟨a,Nat.lt_succ_iff.mpr ha⟩,⟨r,hr⟩)
      have before (j : ℕ) (hj : j ≤ a) : Sight
          (unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n j (r+1))
          (freshet Q.draws Q.paid N m j (r+1)) σ (B*V^D) := by
        let p : T := (⟨j,Nat.lt_succ_iff.mpr (hj.trans ha)⟩,⟨r,hr⟩)
        exact ((price p N cut n V hV paid).mono (enough p).1).more ((enough p).2 V hV)
      apply (WilsonFiniteCommonKineticReset.retained _ _ cut n a r (fun _ => B*V^D) before).more
      change WilsonFiniteCommonKineticReset.fee (ratioHigh Q.draws Q.paid N m) a (r+1)
        (fun _ => B*V^D) ≤ _
      have R : rimJ (ratioHigh Q.draws Q.paid N m) a (r+1) ≤ H := (reset t N cut).trans
        ((Finset.single_le_sum (fun b _ => hcost b) (mem_univ t)).trans (le_add_of_nonneg_left zero_le_one))
      have step := mul_le_mul_of_nonneg_right R b0
      simpa only [WilsonFiniteCommonKineticReset.fee,rimJ,Finset.sum_mul,mul_assoc] using step
    · have finite := (old Q.draws Q.paid Q.hG Q.green N m cut.le).basis n
      rw [finite.lamp a (r+1) (by omega),post_end (A:=Q.draws) Q.hG Q.green cut.le a (r+1) (by omega)]
      exact Sight.zero.more all0

end YM.Integration.WilsonFiniteVacuumWindingReset
end

