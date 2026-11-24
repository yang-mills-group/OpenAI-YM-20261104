import YM.MatchingLedger.Mountain.Copper
import YM.MatchingLedger.Mountain.Ivory
import YM.Push.STATIONARY_UNIFORM.Support
import YM.Comparison.RG02.Assembly.Contact
import YM.Extra.ITERATION_NO_LOSS.Sums
import YM.Integration.NativeNormalizedBondTest

/-!
Original coarse-loop jets on a physical field supported at one spatial site.
Every rank-two loop atom, every original root and the complete normalized
Signed average remain. Native Bounds.two pays the true path lengths, so the
root sum uses lattice decay rather than a volume factor. The final explicit
degree is k+6, with a positive constant chosen before the Run and its period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeOriginalLoopBondJets

open Function Filter Set Metric Lattice Wilson RG Precision Exterior
open MatchingLedger.Mountain Push.Uniform Comparison.RG02.Assembly
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {p : Clip} {W : PathData G}
variable {sigma C Lambda mu : ℝ}

private theorem slot_local (q : Signed) (a : Site n) (s : Slot) {L : ℕ}
    (hs : s.length ≤ L) (U V : Config G n)
    (h : ∀ e : Edge (Site n), separation (affine q 0 a) e.1 ≤ 2 * L → U e = V e) :
    s.atSite (pull q 0 U) a = s.atSite (pull q 0 V) a := by
  rw [Work.F02.atSite_curvature, Work.F02.atSite_curvature]
  apply congrArg G.curvature
  rw [travel_pull, travel_pull]
  apply path_same
  intro e he
  apply h e
  have ht : (Work.F02.slotWalk s).length ≤ 2 * s.length := by
    simp only [Work.F02.slotWalk, List.length_append, Lattice.reverse,
      List.length_map, List.length_reverse]
    change s.walk.length + 4 + s.walk.length ≤ 2 * (s.walk.length + 4)
    omega
  apply he.trans
  simpa only [List.length_map] using ht.trans (Nat.mul_le_mul_left 2 hs)

private theorem atom_local (q : Signed) (a : Site n) {k L : ℕ}
    (t : Atom G k) (ht : t.length ≤ L) (U V : Config G n)
    (h : ∀ e : Edge (Site n), separation (affine q 0 a) e.1 ≤ 2 * L → U e = V e) :
    t.unmasked (pull q 0 U) a = t.unmasked (pull q 0 V) a := by
  apply congrArg t.poly
  funext j
  exact slot_local q a (t.leg j)
    ((Finset.single_le_sum (fun i _ => Nat.zero_le ((t.leg i).length))
      (Finset.mem_univ j)).trans ht) U V h

/-- Each original loop row reads only its true-length region. -/
theorem loop_local (q : Signed) (a : Site n) (i : ℕ)
    (A B : fieldDir G n 1)
    (h : ∀ e : Edge (Site n),
      separation (affine q 0 a) e.1 ≤ 2 * Miner.turnL W i →
        represent A e = represent B e) :
    Miner.slid q a W i A = Miner.slid q a W i B := by
  exact atom_local q a (W.loop i) le_rfl (represent A) (represent B) h

private theorem far_jet (q : Signed) (a : Site n) (i : ℕ)
    {k : ℕ} (hk : 0 < k)
    (hf : ContDiffAt ℝ k (Miner.slid q a W i) 0)
    (o : Site n) (B : fieldDir G n 1)
    (hB : ∀ e : Body 1 n, e.1 ≠ o → B e = 0)
    (hfar : ¬ separation (affine q 0 a) o ≤ 2 * Miner.turnL W i) :
    jet (Miner.slid q a W i) k B = 0 := by
  let P : fieldDir G n 1 →L[ℝ] fieldDir G n 1 :=
    ContinuousLinearMap.pi fun e =>
      if separation (affine q 0 a) e.1 ≤ 2 * Miner.turnL W i
        then ContinuousLinearMap.proj e else 0
  let f := Miner.slid q a W i
  have heq : f = f ∘ P := by
    funext A
    apply loop_local q a i A (P A)
    intro e he
    rw [Work.F03.represent_link, Work.F03.represent_link]
    congr 1
    simp only [P, ContinuousLinearMap.pi_apply, if_pos he,
      ContinuousLinearMap.proj_apply]
  have hP : P B = 0 := by
    funext e
    by_cases he : separation (affine q 0 a) e.1 ≤ 2 * Miner.turnL W i
    · have hn : e.1 ≠ o := by intro ho; apply hfar; simpa only [ho] using he
      simp only [P, ContinuousLinearMap.pi_apply, if_pos he,
        ContinuousLinearMap.proj_apply, hB e hn, Pi.zero_apply]
    · simp only [P, ContinuousLinearMap.pi_apply, if_neg he,
        zero_apply, Pi.zero_apply]
  have hs : ContDiffAt ℝ k f (P 0) := by simpa only [map_zero] using hf
  have hd := congrArg (fun F : fieldDir G n 1 → ℝ => iteratedFDeriv ℝ k F 0) heq
  rw [contact_right P hs, map_zero] at hd
  unfold jet
  change (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 (fun _ => B) = 0
  rw [hd, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    (iteratedFDeriv ℝ k f 0).map_coord_zero ⟨0, hk⟩ hP, smul_zero]

private theorem jet_le {k : ℕ} {f : fieldDir G n 1 → ℝ} {b : ℝ}
    (h : Allows k f 0 b) (B : fieldDir G n 1) (hB : ‖B‖ ≤ 1) :
    ‖jet f k B‖ ≤ (k.factorial : ℝ)⁻¹ * b := by
  let T := iteratedFDeriv ℝ k f 0
  have hv : ‖T (fun _ => B)‖ ≤ b := by
    calc
      _ ≤ ‖T‖ * ‖B‖ ^ k := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          T.le_opNorm (fun _ => B)
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left
        (by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg B) hB k)
        (norm_nonneg T)
      _ = ‖T‖ := mul_one _
      _ ≤ b := h.norm_le k le_rfl
  unfold jet
  rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left hv (by positivity)

/-- The complete original rank-two loop row sum has spatial decay. -/
theorem loop_jet_budget (H : W.Bounds p sigma C Lambda)
    (hmu : 0 < mu) (hwidth : 2 * mu ≤ sigma) (hcap : mu ≤ 1)
    {k : ℕ} (hk : 0 < k) (q : Signed) (a o : Site n)
    (B : fieldDir G n 1) (hnorm : ‖B‖ ≤ 1)
    (hoff : ∀ e : Body 1 n, e.1 ≠ o → B e = 0) :
    SumBudget (fun i : ℕ => ‖jet (Miner.slid q a W i) k B‖)
      ((k.factorial : ℝ)⁻¹ * Miner.compass₁ G k Lambda mu *
        Decay (mu / 2) o (affine q 0 a)) := by
  let h := (Miner.asks q a hmu hwidth hcap k H).2
  let D := Decay (mu / 2) o (affine q 0 a)
  have hD : 0 ≤ D := (decay_pos ..).le
  have hp := Extra.Iteration.Cost.scale' h.budget
    ((k.factorial : ℝ)⁻¹ * D) (mul_nonneg (by positivity) hD)
  have hb : SumBudget (fun i : ℕ => ‖jet (Miner.slid q a W i) k B‖)
      (Miner.compass₁ G k Lambda mu * ((k.factorial : ℝ)⁻¹ * D)) := by
    apply Extra.Iteration.Cost.mono hp (fun _ => norm_nonneg _)
    intro i
    by_cases hi : separation (affine q 0 a) o ≤ 2 * Miner.turnL W i
    · have hd : (separation o (affine q 0 a) : ℝ) ≤ 2 * (Miner.turnL W i : ℝ) := by
        rw [separation_comm]
        exact_mod_cast hi
      have hx : 1 ≤ Real.exp (mu * Miner.turnL W i) * D := by
        unfold D Decay
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith [mul_le_mul_of_nonneg_left hd hmu.le]
      have hw : h.book i ≤ Real.exp (mu * Miner.turnL W i) * h.book i * D := by
        calc
          _ = h.book i * 1 := (mul_one _).symm
          _ ≤ h.book i * (Real.exp (mu * Miner.turnL W i) * D) :=
            mul_le_mul_of_nonneg_left hx (h.straight i)
          _ = _ := by ring
      calc
        _ ≤ (k.factorial : ℝ)⁻¹ * h.book i := jet_le (h.proceeds i 0 (by simp)) B hnorm
        _ ≤ (k.factorial : ℝ)⁻¹ *
            (Real.exp (mu * Miner.turnL W i) * h.book i * D) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
        _ = _ := by ring
    · rw [far_jet q a i hk ((h.proceeds i 0 (by simp)).analytic.of_le le_top)
        o B hoff hi, norm_zero]
      exact mul_nonneg (h.budget.1 i) (mul_nonneg (by positivity) hD)
  exact Extra.Iteration.Cost.enlarge hb (le_of_eq (by dsimp only [D]; ring))

private theorem revenue_jet {I : Type} {k : ℕ} {d : I → ℕ}
    {f : I → fieldDir G n 1 → ℝ} {b : ℝ}
    (h : revenue 1 k mu d f b) (hmu : 0 ≤ mu) (B : fieldDir G n 1) :
    jet (fun A => ∑' i, f i A) k B = ∑' i, jet (f i) k B := by
  have hs := h.reads hmu (by simp : (0 : fieldDir G n 1) ∈ ball 0 1) le_rfl
  unfold jet
  rw [h.ready hmu (by simp : (0 : fieldDir G n 1) ∈ ball 0 1) le_rfl,
    ContinuousMultilinearMap.tsum_eval hs]
  exact (tsum_const_smul'' ((k.factorial : ℝ)⁻¹)).symm

private theorem finite_jet {I : Type*} [Fintype I] {k : ℕ}
    (f : I → fieldDir G n 1 → ℝ) (hf : ∀ i, ContDiffAt ℝ k (f i) 0)
    (B : fieldDir G n 1) :
    jet (fun A => ∑ i, f i A) k B = ∑ i, jet (f i) k B := by
  let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => fieldDir G n 1) ℝ (fun _ => B)
  unfold jet
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => hf i)]
  change (k.factorial : ℝ)⁻¹ • E (∑ i, iteratedFDeriv ℝ k (f i) 0) = _
  rw [map_sum, Finset.smul_sum]
  rfl

private theorem scalar_jet {k : ℕ} (a : ℝ) (f : fieldDir G n 1 → ℝ)
    (hf : ContDiffAt ℝ k f 0) (B : fieldDir G n 1) :
    jet (fun A => a * f A) k B = a * jet f k B := by
  let L : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
  change jet (L ∘ f) k B = L (jet f k B)
  exact (jet_apply_left L f k hf B).symm

/-- Exact factorial-normalized jets of the full original loop. -/
theorem loop_jet_expansion (H : W.Bounds p sigma C Lambda)
    (hmu : 0 < mu) (hwidth : 2 * mu ≤ sigma) (hcap : mu ≤ 1)
    (k : ℕ) (B : fieldDir G n 1) :
    jet (fun A : fieldDir G n 1 => loop W (represent A)) k B =
      Patch.average (fun q : Signed => ∑ a : Site n,
        ∑' i : ℕ, jet (Miner.slid q a W i) k B) := by
  let F (q : Signed) (a : Site n) (A : fieldDir G n 1) :=
    ∑' i : ℕ, Miner.slid q a W i A
  have hf (q : Signed) (a : Site n) : ContDiffAt ℝ k (F q a) 0 :=
    (((Miner.asks q a hmu hwidth hcap k H).2.faint hmu.le 0 (by simp)).smooth)
  have hq (q : Signed) : ContDiffAt ℝ k (fun A => ∑ a, F q a A) 0 :=
    ContDiffAt.sum (s := Finset.univ) (fun a _ => hf q a)
  have hall : ContDiffAt ℝ k (fun A => ∑ q, ∑ a, F q a A) 0 :=
    ContDiffAt.sum (s := Finset.univ) (fun q _ => hq q)
  have he : (fun A : fieldDir G n 1 => loop W (represent A)) =
      (fun A => Patch.average (fun q : Signed => ∑ a, F q a A)) := by
    funext A
    exact Miner.loaded (W := W) A
  rw [he]
  unfold Patch.average
  rw [scalar_jet _ _ hall B, finite_jet _ hq B]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [finite_jet _ (hf q) B]
  apply Finset.sum_congr rfl
  intro a _
  exact revenue_jet (Miner.asks q a hmu hwidth hcap k H).2 hmu.le B

/-- A field supported at one site pays only the lattice decay sum. -/
theorem centered_jet (H : W.Bounds p sigma C Lambda)
    (hmu : 0 < mu) (hwidth : 2 * mu ≤ sigma) (hcap : mu ≤ 1)
    (k : ℕ) (o : Site n) (B : fieldDir G n 1) (hnorm : ‖B‖ ≤ 1)
    (hoff : ∀ e : Body 1 n, e.1 ≠ o → B e = 0) :
    ‖jet (fun A : fieldDir G n 1 => loop W (represent A)) k B -
        jet (fun A : fieldDir G n 1 => loop W (represent A)) k 0‖ ≤
      (k.factorial : ℝ)⁻¹ * Miner.compass₁ G k Lambda mu * countCost (mu / 2) := by
  have hC : 0 ≤ Miner.compass₁ G k Lambda mu :=
    (Miner.asks (n := n) 1 0 hmu hwidth hcap k H).2.burden
  have hK : 0 ≤ (k.factorial : ℝ)⁻¹ * Miner.compass₁ G k Lambda mu :=
    mul_nonneg (by positivity) hC
  by_cases hk : k = 0
  · subst k
    simp only [jet_zero, sub_self, norm_zero]
    exact mul_nonneg hK (count_pos (half_pos hmu)).le
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hz : jet (fun A : fieldDir G n 1 => loop W (represent A)) k 0 = 0 := by
    unfold jet
    rw [(iteratedFDeriv ℝ k (fun A : fieldDir G n 1 => loop W (represent A)) 0).map_coord_zero ⟨0, hkpos⟩ rfl, smul_zero]
  rw [hz, sub_zero, loop_jet_expansion H hmu hwidth hcap k B]
  let K := (k.factorial : ℝ)⁻¹ * Miner.compass₁ G k Lambda mu * countCost (mu / 2)
  have hq (q : Signed) :
      ‖∑ a : Site n, ∑' i : ℕ, jet (Miner.slid q a W i) k B‖ ≤ K := by
    have hi : Injective (affine (R := Per n) q 0) := by
      intro a b hab
      unfold Lattice.affine at hab
      have he := add_right_cancel hab
      simpa using congrArg q⁻¹.act he
    have hc : (∑ a : Site n, Decay (mu / 2) o (affine q 0 a)) ≤ countCost (mu / 2) := by
      simpa only [Nat.cast_one, one_mul] using
        (Multiplicity.injective hi).count (affine (R := Per n) q 0) (half_pos hmu) o
    calc
      _ ≤ ∑ a : Site n, ‖∑' i : ℕ, jet (Miner.slid q a W i) k B‖ := norm_sum_le _ _
      _ ≤ ∑ a : Site n, (k.factorial : ℝ)⁻¹ * Miner.compass₁ G k Lambda mu *
          Decay (mu / 2) o (affine q 0 a) := by
        apply Finset.sum_le_sum
        intro a _
        have h := loop_jet_budget H hmu hwidth hcap hkpos q a o B hnorm hoff
        exact (norm_tsum_le_tsum_norm h.2.1).trans h.2.2
      _ = ((k.factorial : ℝ)⁻¹ * Miner.compass₁ G k Lambda mu) *
          ∑ a : Site n, Decay (mu / 2) o (affine q 0 a) := (Finset.mul_sum ..).symm
      _ ≤ K := mul_le_mul_of_nonneg_left hc hK
  let t : ℝ := Fintype.card Signed
  have ht : 0 < t := by unfold t; positivity
  unfold Patch.average
  calc
    _ = t⁻¹ * ‖∑ q : Signed, ∑ a : Site n,
        ∑' i : ℕ, jet (Miner.slid q a W i) k B‖ := by
      rw [norm_mul, Real.norm_of_nonneg (inv_pos.mpr ht).le]
    _ ≤ t⁻¹ * (∑ q : Signed, ‖∑ a : Site n,
        ∑' i : ℕ, jet (Miner.slid q a W i) k B‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_pos.mpr ht).le
    _ ≤ t⁻¹ * (∑ _q : Signed, K) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hq q)) (inv_pos.mpr ht).le
    _ = K := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ ht.ne']

def priceWidth (sigma : ℝ) : ℝ := min (sigma / 2) 1

def price (G : Gauge) (k : ℕ) (Lambda sigma : ℝ) : ℝ :=
  (k.factorial : ℝ)⁻¹ * Miner.compass₁ G k Lambda (priceWidth sigma) *
    countCost (priceWidth sigma / 2)

/-- No extra width hypothesis: the cap is taken inside the price only. -/
theorem centered_jet_capped (H : W.Bounds p sigma C Lambda)
    (k : ℕ) (o : Site n) (B : fieldDir G n 1) (hnorm : ‖B‖ ≤ 1)
    (hoff : ∀ e : Body 1 n, e.1 ≠ o → B e = 0) :
    ‖jet (fun A : fieldDir G n 1 => loop W (represent A)) k B -
        jet (fun A : fieldDir G n 1 => loop W (represent A)) k 0‖ ≤
      price G k Lambda sigma := by
  have hp : 0 < priceWidth sigma := lt_min (half_pos H.width) zero_lt_one
  have ht : 2 * priceWidth sigma ≤ sigma := by
    have h := min_le_left (sigma / 2) (1 : ℝ)
    dsimp only [priceWidth]
    linarith
  exact centered_jet H hp ht (min_le_right _ _) k o B hnorm hoff

private theorem inverse_width {sigma : ℝ} (hs : 0 < sigma) :
    (priceWidth sigma)⁻¹ ≤ 2 * (1 + sigma⁻¹) := by
  have hi : 0 ≤ sigma⁻¹ := (inv_pos.mpr hs).le
  unfold priceWidth
  by_cases h : sigma / 2 ≤ 1
  · rw [min_eq_left h, inv_div, div_eq_mul_inv]
    linarith
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), inv_one]
    linarith

/-- A fixed, explicit degree controls the price before every positive width.
The constant includes the native gauge paint/slot costs, without a Run or
period parameter. -/
theorem price_growth (G : Gauge) (k : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ sigma : ℝ, 0 < sigma →
      price G k 1 sigma ≤ C0 * (1 + sigma⁻¹)^(k+6) := by
  let D : ℝ := 1 + 4 * (2 : ℝ)^k
  let V : ℝ := |Work.F02.slotConst G|^2 * (k.factorial : ℝ) *
    D^k * (1 + Miner.amount G k)^k
  let E : ℝ := Real.exp 1 * ((6 : ℕ).factorial : ℝ) * (2 : ℝ)^16
  let K : ℝ := (k.factorial : ℝ)⁻¹ * V * E
  have hamount : 0 < Miner.amount G k :=
    outer_pos G k (Miner.paintStamp G k).1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨1+K, by positivity, ?_⟩
  intro sigma hs
  let mu := priceWidth sigma
  let B : ℝ := 1 + sigma⁻¹
  have hmu : 0 < mu := lt_min (half_pos hs) zero_lt_one
  have hmucap : mu ≤ 1 := min_le_right _ _
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (inv_pos.mpr hs).le
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hmi : mu⁻¹ ≤ 2*B := inverse_width hs
  have hradius : mu/2 ≤ Work.F02.radius mu := by
    have he := Real.add_one_le_exp (mu/2)
    unfold Work.F02.radius
    linarith
  have hri : (Work.F02.radius mu)⁻¹ ≤ 2*mu⁻¹ := by
    simpa only [one_div, inv_div, div_eq_mul_inv, one_mul, mul_inv_rev, inv_inv] using
      (one_div_le_one_div_of_le (half_pos hmu) hradius)
  have hrB : (Work.F02.radius mu)⁻¹ ≤ 4*B := by
    calc
      _ ≤ 2*mu⁻¹ := hri
      _ ≤ 2*(2*B) := mul_le_mul_of_nonneg_left hmi zero_le_two
      _ = _ := by ring
  have hbase : 1 + (2 : ℝ)^k / Work.F02.radius mu ≤ D*B := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ 1 + (2 : ℝ)^k * (4*B) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hrB (by positivity))
      _ ≤ B + (2 : ℝ)^k * (4*B) := add_le_add hB le_rfl
      _ = _ := by dsimp [D]; ring
  have hpow : (1 + (2 : ℝ)^k / Work.F02.radius mu)^k ≤ D^k * B^k := by
    calc
      _ ≤ (D*B)^k := pow_le_pow_left₀
        (by have hp := Work.F02.radius_pos hmu; positivity) hbase k
      _ = _ := mul_pow _ _ _
  have hvalue : Miner.value G k 2 mu ≤ V * B^k := by
    dsimp only [Miner.value, Miner.richness, composeCost]
    calc
      _ ≤ |Work.F02.slotConst G|^2 *
          ((k.factorial : ℝ) * (D^k * B^k) * (1 + Miner.amount G k)^k) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity))
          (sq_nonneg _)
      _ = _ := by dsimp [V]; ring
  have hhalf : (mu/2)⁻¹ ≤ 4*B := by
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ 2*(2*B) := mul_le_mul_of_nonneg_left hmi zero_le_two
      _ = _ := by ring
  have hcount : countCost (mu/2) ≤ E * B^6 := by
    have hexp : Real.exp ((mu/2)*2) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith)
    have hpower := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ (mu/2)⁻¹) hhalf 6
    calc
      _ = (Real.exp ((mu/2)*2) * ((6 : ℕ).factorial : ℝ)) *
          ((mu/2)⁻¹)^6 * (2 : ℝ)^4 := by
        simp only [countCost, div_eq_mul_inv, inv_pow]
      _ ≤ (Real.exp 1 * ((6 : ℕ).factorial : ℝ)) * (4*B)^6 * (2 : ℝ)^4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_right hexp (by positivity))
            hpower (by positivity) (by positivity)) (by positivity)
      _ = _ := by dsimp [E]; rw [mul_pow]; ring
  have hprice : price G k 1 sigma ≤ K * B^(k+6) := by
    calc
      _ = (k.factorial : ℝ)⁻¹ * Miner.value G k 2 mu * countCost (mu/2) := by
        simp only [mu, price, Miner.compass₁, one_mul]
      _ ≤ ((k.factorial : ℝ)⁻¹ * (V * B^k)) * (E * B^6) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hvalue (by positivity))
          hcount (count_pos (half_pos hmu)).le (by positivity)
      _ = _ := by dsimp [K]; rw [pow_add]; ring
  exact hprice.trans (mul_le_mul_of_nonneg_right
    (by linarith : K ≤ 1+K) (pow_nonneg hB0 _))

/-- One constant is chosen before the Run, original cutoff, period and level.
The entire signed loop and the actual one-bond field are retained. -/
theorem atRun (G : Gauge) (k : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (R : PhysicalNext.Repeat.Legato.Run G) (hG : G.Simple)
        (N period m : ℕ), m ≤ N →
        ‖jet (fun A : fieldDir G (R.family.side m period) 1 =>
              loop (R.family.path.rep N period m).path (represent A)) k
            (NativeNormalizedBondTest.actualField R hG m period) -
          jet (fun A : fieldDir G (R.family.side m period) 1 =>
              loop (R.family.path.rep N period m).path (represent A)) k 0‖ ≤
          (R.family.path.levels.clock.loopCap m) * C0 *
            (1 + (R.family.path.levels.params m).width⁻¹)^(k+6) := by
  obtain ⟨C0, hC0, hprice⟩ := price_growth G k
  refine ⟨C0, hC0, ?_⟩
  intro R hG N period m hm
  have hc : R.family.path.Conv N period m := R.makes.wilson.represents N period m hm
  have hp : (R.family.path.rep N period m).path.Bounds
      (R.family.path.levels.params m).clip (R.family.path.levels.params m).width
      (R.family.path.levels.params m).paths (R.family.path.levels.clock.loopCap m) := by
    rw [← hc.clip]
    exact hc.good.paths
  have hB := NativeNormalizedBondTest.actual_facts R hG m period
  have hj := centered_jet_capped hp k 0
    (NativeNormalizedBondTest.actualField R hG m period) hB.1.le
    (by
      intro e he
      apply hB.2.2.1 e
      intro h
      apply he
      exact congrArg Prod.fst h)
  have hLambda : 0 ≤ R.family.path.levels.clock.loopCap m :=
    (tsum_nonneg hp.two.1).trans hp.two.2.2
  calc
    _ ≤ price G k (R.family.path.levels.clock.loopCap m)
        (R.family.path.levels.params m).width := hj
    _ = (R.family.path.levels.clock.loopCap m) *
        price G k 1 (R.family.path.levels.params m).width := by
      dsimp only [price, Miner.compass₁]
      ring
    _ ≤ (R.family.path.levels.clock.loopCap m) *
        (C0 * (1 + (R.family.path.levels.params m).width⁻¹)^(k+6)) :=
      mul_le_mul_of_nonneg_left (hprice _ hp.width) hLambda
    _ = _ := by ring

end YM.Integration.NativeOriginalLoopBondJets
end
