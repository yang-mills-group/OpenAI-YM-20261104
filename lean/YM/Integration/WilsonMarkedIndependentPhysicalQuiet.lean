import YM.Integration.WilsonMarkedIndependentPhysicalIntake
import YM.Integration.WilsonFiniteVacuumWindingReset

/-! Return the one physical fine-side vacuum along the same measured update as the occupied rows. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentPhysicalQuiet
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open scoped Classical BigOperators
open WilsonMarkedIndependentPhysicalIntake (PositiveAt)
variable {G : Gauge} {e m i r : ℕ} {E : Credit}

/-- Constants and output width precede the cutoff, period and inlet bill. -/
theorem prior (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) (hi : i ≤ e) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 0 ≤ C ∧ 0 < σ ∧ ∀ N (_ : m < N) (n : Side) (V : ℝ),
      1 ≤ V → PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V →
      Sight (unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n i r)
        (freshet Q.draws Q.paid N m i r) σ (C*V^d) := by
  obtain ⟨B,hB,frame⟩ := WilsonMarkedIndependentPhysicalIntake.prepare Q hm hs
  obtain ⟨d,step⟩ := windingVault G e i r hi
  obtain ⟨σ,C,hσ,hC,pay⟩ := step (holt Q m hm s hs)
  refine ⟨d,C*B^d,σ,mul_nonneg hC (pow_nonneg (zero_le_one.trans hB) _),hσ,?_⟩
  intro N cut n V hV issued
  let p : ScrollV e (holt Q m hm s hs) :=
    { cloVent Q m N n hm cut s hs with W := (story Q.draws Q.paid N (m+1)).1
                                       coin := B*V
                                       paid := one_le_mul_of_one_le_of_one_le hB hV
                                       fare := frame N cut n V hV issued }
  have charged := pay p
  change Sight (unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n i r)
    (freshet Q.draws Q.paid N m i r) σ (C*(B*V)^d) at charged
  simpa only [mul_pow,mul_assoc] using charged

/-- One before-cutoff loan covers every retained angular tensor of the actual and
the independently prescribed vacua after the very same cover kinetic reversion. -/
theorem posted (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) {s : ℝ} (hs : 0 < s) :
    ∃ (D : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, m < N → ∀(n:Side) (V:ℝ),1 ≤ V →
      PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V →
      ∀ a,a ≤ e → ∀ l,
      Sight ((story Q.draws Q.paid N m).1 n a l) (actionW Q.draws Q.paid N m a l) σ (C*V^D) := by
  classical
  let T := Fin (e+1) × Fin (e+2)
  choose d C s' hc hs' price using fun t : T => prior
    (r:=t.2.val+1) Q hm (Nat.lt_succ_iff.mp t.1.isLt) hs
  obtain ⟨σ,B,D,hσ,hB,enough⟩ := WilsonFiniteVacuumWindingReset.common s' C d hs' hc
  choose cost hcost reset using fun t : T => WilsonFiniteVacuumWindingReset.rim Q hm (Nat.lt_succ_iff.mp t.1.isLt) (t.2.val+1)
  let H := 1+∑ t : T, cost t
  have hH : 1 ≤ H := le_add_of_nonneg_right (Finset.sum_nonneg fun t _ => hcost t)
  refine ⟨D,H*B,σ,one_le_mul_of_one_le_of_one_le hH hB,hσ,?_⟩
  intro N cut n V hV paid a ha l
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

end YM.Integration.WilsonMarkedIndependentPhysicalQuiet
end
