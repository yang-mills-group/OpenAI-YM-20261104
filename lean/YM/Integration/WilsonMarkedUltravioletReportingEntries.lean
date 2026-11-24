import YM.Integration.WilsonMarkedUltravioletReportingReserve
import YM.Integration.WilsonMarkedUltravioletMixedWallet

/-! The two complete original mixed arrays have small unweighted site budgets at the
tuning date. Their joint restore retains every single mark and the original vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedUltravioletReportingEntries
open Finset Function Filter Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil
open RG05Readout.Many PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem spend {n : Side} {V I : Type} [DecidableEq V] [Fintype I] {J : Census V}
    {o : V → Site n} {S : I → Support n} {F : I → Config G n → Poly J} {w : V → ℝ}
    {B D : ℕ} {α t M ε : ℝ} (bank : Towed w S F B α 1) (wp : ∀ v, 0 < w v)
    (Mpos : 0 ≤ M) (cost : M*Real.exp (-(D:ℝ)) ≤ ε)
    (sizes : ∀ s : J.Mode, 1 ≤ M*Poly.toll w s)
    (whereabouts : ∀ i, Borne o (S i) (F i) t)
    (occupied : ∀ i U, rises (F i U))
    (apart : ∀ s : J.Mode, 2 ≤ s.val.card →
      ∃ a ∈ s.val, ∃ b ∈ s.val, D*(4*B+2)+2*B < separation (o a) (o b)) :
    Towed (fun _ : V => (1:ℝ)) S F B (α-1) ε := by
  have reach := WilsonMarkedUltravioletMixedWallet.reach whereabouts
    (fun i U s nonzero => apart s (occupied i U s nonzero))
  obtain ⟨wallet,finite,hit,paid⟩ := WilsonMarkedUltravioletMixedWallet.purchase
    bank wp (σ:=1) zero_le_one Mpos (fun _ _ s _ => sizes s) reach
  refine ⟨wallet,finite,fun x => budget_loosen (hit x) ?_,paid⟩
  simpa only [mul_one,neg_one_mul] using cost

theorem original (R : Run G) (simple : G.Simple) (p k h L : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, let A := R.family.path.levels
      ∀ N : ℕ, m < N → ∀ per d : ℕ,
        let P := R.family.path.rep N per m
        let α := (A.budget m).supportExponent
        let g := (Real.sqrt P.beta)⁻¹
        ∀ {V : Type} [DecidableEq V] [Fintype V] {J : Census V}
          (Q : V → ℝ) (o : V → Site (R.family.side m per))
          (rows : V → RG05Readout.Address.Three G (R.family.side m per))
          (Z : Config G (R.family.side m per) → Poly J),
          (∀ v, 0 < Q v) → (∀ v, Q v ≤ (A.clock.hatBeta m)^h) →
          MenuBoard P rows Z o (fun v => RG05Readout.Many.envelope R.family m d k (Q v) m) α 1 →
          (∀ s : J.Mode, s.val.card ≤ L) →
          (∀ s : J.Mode, 2 ≤ s.val.card →
            ∃ a ∈ s.val, ∃ b ∈ s.val, (A.budget m).B^2+1 ≤ separation (o a) (o b)) →
          ∃ H K, Carton o H K P.p.threshold ∧
            Z=restore P (fun v => (rows v).2.1) (fun v => profile P.activities (rows v).2.2) H K ∧
            Towed (fun _ : V => (1:ℝ)) id H P.p.B (α-1) (ε*g^p) ∧
            Towed (fun _ : V => (1:ℝ)) (fun i : Box (R.family.side m per) => i.1)
              K P.p.B (α-1) (ε*g^p) := by
  filter_upwards [WilsonMarkedUltravioletReportingReserve.calendar R simple p ((k+h)*L) ep]
    with m allowance A N live per d P α g V de fi J Q o rows Z positive size board count placement
  obtain ⟨D,housing,fee⟩ := allowance
  let M := (A.clock.hatBeta m)^((k+h)*L)
  let w := fun v => RG05Readout.Many.envelope R.family m d k (Q v) m
  have mp : 0 ≤ M := pow_nonneg (zero_lt_one.trans (A.fits.delayed m)).le _
  have wp (v : V) : 0 < w v := by
    unfold w RG05Readout.Many.envelope RG05Readout.Many.west
    rw [rust_above (le_refl m),one_mul]
    exact grantw (totalpos (positive v) m)
  have expenses (s : J.Mode) : 1 ≤ M*Poly.toll w s :=
    WilsonMarkedUltravioletReportingReserve.weights R.family m d k h L Q positive size s (count s)
  have same : P.p = A.budget m := (R.T.choice.represents N per m live.le).vac
  have apart (s : J.Mode) (two : 2 ≤ s.val.card) :
      ∃ a ∈ s.val, ∃ b ∈ s.val, D*(4*P.p.B+2)+2*P.p.B < separation (o a) (o b) := by
    obtain ⟨a,ha,b,hb,separate⟩ := placement s two
    refine ⟨a,ha,b,hb,?_⟩
    rw [same]
    exact lt_of_le_of_lt housing (Nat.lt_of_succ_le separate)
  obtain ⟨H,K,originals,regular,forced,allFields⟩ := board.grants
  refine ⟨H,K,originals,allFields,?_,?_⟩
  · exact spend regular wp mp (fee N live.le per) expenses
      (fun i => (originals.exp i).1.toBorne) (fun i => (originals.exp i).2) apart
  · exact spend forced wp mp (fee N live.le per) expenses
      (fun i => (originals.flag i).1.toBorne) (fun i => (originals.flag i).2) apart

end YM.Integration.WilsonMarkedUltravioletReportingEntries
