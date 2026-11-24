import YM.MatchingLedger.Mountain.Ivory
import YM.Push.STATIONARY_UNIFORM.Support
import YM.Comparison.RG02.Assembly.Contact
import YM.Extra.ITERATION_NO_LOSS.Sums
import YM.Integration.NativeNormalizedBondTest

/-! Original main-action jets on a field supported at one spatial site.
The literal Metal rows retain direct plaquettes, both ordered ell rows, and
all cubic/quartic atoms. Their original exponential revenue pays the root
sum; no full-volume operator bound is used. All jets keep the native 1/k!
normalization, and the width cap changes only the price calculation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeOriginalMainBondJets

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

/-- The original signed row reads only its true-length region. -/
theorem metal_local (q : Signed) (a : Site n) (i : Miner.Metal)
    (A B : fieldDir G n 1)
    (h : ∀ e : Edge (Site n),
      separation (affine q 0 a) e.1 ≤ 2 * Miner.travels W i →
        represent A e = represent B e) :
    Miner.slope q a p W i A = Miner.slope q a p W i B := by
  rcases i with b | i
  · change p.direct * G.price (faceValue (pull q 0 (represent A)) (a, b)) =
      p.direct * G.price (faceValue (pull q 0 (represent B)) (a, b))
    apply congrArg (fun z : G.El => p.direct * G.price z)
    unfold faceValue
    rw [travel_pull, travel_pull]
    apply path_same
    intro e he
    apply h e
    exact he.trans (by simp [Miner.travels, square])
  rcases i with i | i
  · rcases i with ⟨b, r, s⟩
    have hr := slot_local q a (W.row b r).2
      (L := Miner.travels W (Sum.inr (Sum.inl (b, r, s))))
      (by dsimp [Miner.travels, Miner.fare₁, Miner.high]; omega)
      (represent A) (represent B) h
    have hs := slot_local q a (W.row b s).2
      (L := Miner.travels W (Sum.inr (Sum.inl (b, r, s))))
      (by dsimp [Miner.travels, Miner.fare₁, Miner.high]; omega)
      (represent A) (represent B) h
    change Miner.beam * inner ℝ
      ((W.row b r).1 • (W.row b r).2.atSite (pull q 0 (represent A)) a)
      ((W.row b s).1 • (W.row b s).2.atSite (pull q 0 (represent A)) a) =
        Miner.beam * inner ℝ
          ((W.row b r).1 • (W.row b r).2.atSite (pull q 0 (represent B)) a)
          ((W.row b s).1 • (W.row b s).2.atSite (pull q 0 (represent B)) a)
    rw [hr, hs]
  rcases i with i | i
  · exact atom_local q a (W.cubic i) le_rfl (represent A) (represent B) h
  · exact atom_local q a (W.quartic i) le_rfl (represent A) (represent B) h

private theorem far_jet (q : Signed) (a : Site n) (i : Miner.Metal)
    {k : ℕ} (hk : 0 < k)
    (hf : ContDiffAt ℝ k (Miner.slope q a p W i) 0)
    (o : Site n) (B : fieldDir G n 1)
    (hB : ∀ e : Body 1 n, e.1 ≠ o → B e = 0)
    (hfar : ¬ separation (affine q 0 a) o ≤ 2 * Miner.travels W i) :
    jet (Miner.slope q a p W i) k B = 0 := by
  let P : fieldDir G n 1 →L[ℝ] fieldDir G n 1 :=
    ContinuousLinearMap.pi fun e =>
      if separation (affine q 0 a) e.1 ≤ 2 * Miner.travels W i
        then ContinuousLinearMap.proj e else 0
  let f := Miner.slope q a p W i
  have heq : f = f ∘ P := by
    funext A
    apply metal_local q a i A (P A)
    intro e he
    rw [Work.F03.represent_link, Work.F03.represent_link]
    congr 1
    simp only [P, ContinuousLinearMap.pi_apply, if_pos he,
      ContinuousLinearMap.proj_apply]
  have hP : P B = 0 := by
    funext e
    by_cases he : separation (affine q 0 a) e.1 ≤ 2 * Miner.travels W i
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

/-- The full absolute row sum at one original root has spatial decay. -/
theorem metal_jet_budget (H : W.Bounds p sigma C Lambda)
    (hmu : 0 < mu) (hwidth : 2 * mu ≤ sigma) (hcap : mu ≤ 1)
    {k : ℕ} (hk : 0 < k) (q : Signed) (a o : Site n)
    (B : fieldDir G n 1) (hnorm : ‖B‖ ≤ 1)
    (hoff : ∀ e : Body 1 n, e.1 ≠ o → B e = 0) :
    SumBudget (fun i : Miner.Metal => ‖jet (Miner.slope q a p W i) k B‖)
      ((k.factorial : ℝ)⁻¹ * Miner.compass₀ G k C mu *
        Decay (mu / 2) o (affine q 0 a)) := by
  let h := (Miner.asks q a hmu hwidth hcap k H).1
  let D := Decay (mu / 2) o (affine q 0 a)
  have hD : 0 ≤ D := (decay_pos ..).le
  have hp := Extra.Iteration.Cost.scale' h.budget
    ((k.factorial : ℝ)⁻¹ * D) (mul_nonneg (by positivity) hD)
  have hb : SumBudget (fun i : Miner.Metal => ‖jet (Miner.slope q a p W i) k B‖)
      (Miner.compass₀ G k C mu * ((k.factorial : ℝ)⁻¹ * D)) := by
    apply Extra.Iteration.Cost.mono hp (fun _ => norm_nonneg _)
    intro i
    by_cases hi : separation (affine q 0 a) o ≤ 2 * Miner.travels W i
    · have hd : (separation o (affine q 0 a) : ℝ) ≤ 2 * (Miner.travels W i : ℝ) := by
        rw [separation_comm]
        exact_mod_cast hi
      have hx : 1 ≤ Real.exp (mu * Miner.travels W i) * D := by
        unfold D Decay
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith [mul_le_mul_of_nonneg_left hd hmu.le]
      have hw : h.book i ≤ Real.exp (mu * Miner.travels W i) * h.book i * D := by
        calc
          _ = h.book i * 1 := (mul_one _).symm
          _ ≤ h.book i * (Real.exp (mu * Miner.travels W i) * D) :=
            mul_le_mul_of_nonneg_left hx (h.straight i)
          _ = _ := by ring
      calc
        _ ≤ (k.factorial : ℝ)⁻¹ * h.book i := jet_le (h.proceeds i 0 (by simp)) B hnorm
        _ ≤ (k.factorial : ℝ)⁻¹ *
            (Real.exp (mu * Miner.travels W i) * h.book i * D) :=
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

/-- Exact jets of every original row, before taking absolute values. -/
theorem main_jet_expansion (H : W.Bounds p sigma C Lambda)
    (hmu : 0 < mu) (hwidth : 2 * mu ≤ sigma) (hcap : mu ≤ 1)
    (k : ℕ) (B : fieldDir G n 1) :
    jet (fun A : fieldDir G n 1 => mainTerm p W (represent A)) k B =
      Patch.average (fun q : Signed => ∑ a : Site n,
        ∑' i : Miner.Metal, jet (Miner.slope q a p W i) k B) := by
  let F (q : Signed) (a : Site n) (A : fieldDir G n 1) :=
    ∑' i : Miner.Metal, Miner.slope q a p W i A
  have hf (q : Signed) (a : Site n) : ContDiffAt ℝ k (F q a) 0 :=
    (((Miner.asks q a hmu hwidth hcap k H).1.faint hmu.le 0 (by simp)).smooth)
  have hq (q : Signed) : ContDiffAt ℝ k (fun A => ∑ a, F q a A) 0 :=
    ContDiffAt.sum (s := Finset.univ) (fun a _ => hf q a)
  have hall : ContDiffAt ℝ k (fun A => ∑ q, ∑ a, F q a A) 0 :=
    ContDiffAt.sum (s := Finset.univ) (fun q _ => hq q)
  have he : (fun A : fieldDir G n 1 => mainTerm p W (represent A)) =ᶠ[𝓝 0]
      (fun A => Patch.average (fun q : Signed => ∑ a, F q a A)) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1))] with A hA
    exact Miner.recorded hmu hwidth k H hA
  calc
    _ = jet (fun A => Patch.average (fun q : Signed => ∑ a, F q a A)) k B := by
      unfold jet
      rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
    _ = _ := by
      unfold Patch.average
      rw [scalar_jet _ _ hall B, finite_jet _ hq B]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      rw [finite_jet _ (hf q) B]
      apply Finset.sum_congr rfl
      intro a _
      exact revenue_jet (Miner.asks q a hmu hwidth hcap k H).1 hmu.le B

/-- A field supported at one site pays only the lattice decay sum. -/
theorem centered_jet (H : W.Bounds p sigma C Lambda)
    (hmu : 0 < mu) (hwidth : 2 * mu ≤ sigma) (hcap : mu ≤ 1)
    (k : ℕ) (o : Site n) (B : fieldDir G n 1) (hnorm : ‖B‖ ≤ 1)
    (hoff : ∀ e : Body 1 n, e.1 ≠ o → B e = 0) :
    ‖jet (fun A : fieldDir G n 1 => mainTerm p W (represent A)) k B -
        jet (fun A : fieldDir G n 1 => mainTerm p W (represent A)) k 0‖ ≤
      (k.factorial : ℝ)⁻¹ * Miner.compass₀ G k C mu * countCost (mu / 2) := by
  have hC : 0 ≤ Miner.compass₀ G k C mu :=
    (Miner.asks (n := n) 1 0 hmu hwidth hcap k H).1.burden
  have hK : 0 ≤ (k.factorial : ℝ)⁻¹ * Miner.compass₀ G k C mu :=
    mul_nonneg (by positivity) hC
  by_cases hk : k = 0
  · subst k
    simp only [jet_zero, sub_self, norm_zero]
    exact mul_nonneg hK (count_pos (half_pos hmu)).le
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hz : jet (fun A : fieldDir G n 1 => mainTerm p W (represent A)) k 0 = 0 := by
    unfold jet
    rw [(iteratedFDeriv ℝ k (fun A : fieldDir G n 1 => mainTerm p W (represent A)) 0).map_coord_zero ⟨0, hkpos⟩ rfl, smul_zero]
  rw [hz, sub_zero, main_jet_expansion H hmu hwidth hcap k B]
  let K := (k.factorial : ℝ)⁻¹ * Miner.compass₀ G k C mu * countCost (mu / 2)
  have hq (q : Signed) :
      ‖∑ a : Site n, ∑' i : Miner.Metal, jet (Miner.slope q a p W i) k B‖ ≤ K := by
    have hi : Injective (affine (R := Per n) q 0) := by
      intro a b hab
      unfold Lattice.affine at hab
      have he := add_right_cancel hab
      simpa using congrArg q⁻¹.act he
    have hc : (∑ a : Site n, Decay (mu / 2) o (affine q 0 a)) ≤ countCost (mu / 2) := by
      simpa only [Nat.cast_one, one_mul] using
        (Multiplicity.injective hi).count (affine (R := Per n) q 0) (half_pos hmu) o
    calc
      _ ≤ ∑ a : Site n, ‖∑' i : Miner.Metal, jet (Miner.slope q a p W i) k B‖ := norm_sum_le _ _
      _ ≤ ∑ a : Site n, (k.factorial : ℝ)⁻¹ * Miner.compass₀ G k C mu *
          Decay (mu / 2) o (affine q 0 a) := by
        apply Finset.sum_le_sum
        intro a _
        have h := metal_jet_budget H hmu hwidth hcap hkpos q a o B hnorm hoff
        exact (norm_tsum_le_tsum_norm h.2.1).trans h.2.2
      _ = ((k.factorial : ℝ)⁻¹ * Miner.compass₀ G k C mu) *
          ∑ a : Site n, Decay (mu / 2) o (affine q 0 a) := (Finset.mul_sum ..).symm
      _ ≤ K := mul_le_mul_of_nonneg_left hc hK
  let t : ℝ := Fintype.card Signed
  have ht : 0 < t := by unfold t; positivity
  unfold Patch.average
  calc
    _ = t⁻¹ * ‖∑ q : Signed, ∑ a : Site n,
        ∑' i : Miner.Metal, jet (Miner.slope q a p W i) k B‖ := by
      rw [norm_mul, Real.norm_of_nonneg (inv_pos.mpr ht).le]
    _ ≤ t⁻¹ * (∑ q : Signed, ‖∑ a : Site n,
        ∑' i : Miner.Metal, jet (Miner.slope q a p W i) k B‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_pos.mpr ht).le
    _ ≤ t⁻¹ * (∑ _q : Signed, K) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hq q)) (inv_pos.mpr ht).le
    _ = K := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ ht.ne']

def priceWidth (sigma : ℝ) : ℝ := min (sigma / 2) 1

def price (G : Gauge) (k : ℕ) (C sigma : ℝ) : ℝ :=
  (k.factorial : ℝ)⁻¹ * Miner.compass₀ G k C (priceWidth sigma) *
    countCost (priceWidth sigma / 2)

/-- No extra width hypothesis: the cap is taken inside the price only. -/
theorem centered_jet_capped (H : W.Bounds p sigma C Lambda)
    (k : ℕ) (o : Site n) (B : fieldDir G n 1) (hnorm : ‖B‖ ≤ 1)
    (hoff : ∀ e : Body 1 n, e.1 ≠ o → B e = 0) :
    ‖jet (fun A : fieldDir G n 1 => mainTerm p W (represent A)) k B -
        jet (fun A : fieldDir G n 1 => mainTerm p W (represent A)) k 0‖ ≤
      price G k C sigma := by
  have hp : 0 < priceWidth sigma := lt_min (half_pos H.width) zero_lt_one
  have ht : 2 * priceWidth sigma ≤ sigma := by
    have h := min_le_left (sigma / 2) (1 : ℝ)
    dsimp only [priceWidth]
    linarith
  exact centered_jet H hp ht (min_le_right _ _) k o B hnorm hoff

/-- The same original Run and the already constructed genuine one-bond field. -/
theorem atRun (R : PhysicalNext.Repeat.Legato.Run G) (hG : G.Simple)
    (k N period m : ℕ) (hm : m ≤ N) :
    ‖jet (fun A : fieldDir G (R.family.side m period) 1 =>
          mainTerm (R.family.path.levels.params m).clip
            (R.family.path.rep N period m).path (represent A)) k
        (NativeNormalizedBondTest.actualField R hG m period) -
      jet (fun A : fieldDir G (R.family.side m period) 1 =>
          mainTerm (R.family.path.levels.params m).clip
            (R.family.path.rep N period m).path (represent A)) k 0‖ ≤
      price G k (R.family.path.levels.params m).paths
        (R.family.path.levels.params m).width := by
  have hc : R.family.path.Conv N period m := R.makes.wilson.represents N period m hm
  have hp : (R.family.path.rep N period m).path.Bounds
      (R.family.path.levels.params m).clip (R.family.path.levels.params m).width
      (R.family.path.levels.params m).paths (R.family.path.levels.clock.loopCap m) := by
    rw [← hc.clip]
    exact hc.good.paths
  have hB := NativeNormalizedBondTest.actual_facts R hG m period
  apply centered_jet_capped hp k 0 (NativeNormalizedBondTest.actualField R hG m period) hB.1.le
  intro e he
  apply hB.2.2.1 e
  intro h
  apply he
  exact congrArg Prod.fst h

end YM.Integration.NativeOriginalMainBondJets
end
