import YM.Integration.FVA1Physical.Round2.CalibratedEnvelope

/-! The same physical vacuum invoice pays every realized formal scene. This form allows another verified argument to select its own scene without any uniqueness assumption. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk MSbar.CrossH
open Filter RG Wilson Precision MSbar.Midpoint PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology

private theorem envelope_reference_price {β γ : ℝ} (hβ : 1 ≤ β) (hγ : 0 < γ) (h : γ ≤ 2*β) (p : ℕ) :
    Mosaic.goalP β (p+1) ≤ (2*Heath.Stock.cue γ)^(p+1) := by
  have hp := zero_lt_one.trans_le hβ
  have hs := Real.sqrt_pos.mpr hp
  have ht := Real.sqrt_pos.mpr hγ
  have sqγ := Real.sq_sqrt hγ.le
  have sqβ := Real.sq_sqrt hp.le
  have hroot : Real.sqrt γ ≤ 2*Real.sqrt β := by nlinarith
  have hratio : (Real.sqrt β)⁻¹ ≤ 2*(Real.sqrt γ)⁻¹ := by
    rw [← one_div (Real.sqrt β), ←div_eq_mul_inv, div_le_div_iff₀ hs ht]
    simpa using hroot
  calc
    Mosaic.goalP β (p+1) ≤ β ^ ((-1/2:ℝ)*(p+1)) := by
      apply Real.rpow_le_rpow_of_exponent_le hβ
      unfold Mosaic.pawn
      push_cast; linarith
    _ = ((Real.sqrt β)⁻¹) ^ (p+1) := by
      rw [show ((-1/2:ℝ)*(p+1))=(-1/2)*(↑(p+1:ℕ):ℝ) by push_cast; ring,
        Real.rpow_mul hp.le,Real.rpow_natCast,
        show (-1/2:ℝ)=-(1/2) by ring,Real.rpow_neg hp.le,← Real.sqrt_eq_rpow]
    _ ≤ _ := pow_le_pow_left₀ (inv_nonneg.mpr hs.le) hratio _

theorem allscene_vacuum_envelope {G : Gauge} {C : Family G} {Z : Horizon C.path.levels}
    {u : G.ColorIndex} {O : ChartRatio G} {K : Kin Z O} (hG : G.Simple)
    (physical : C.path.Selected) (D : Docket C u O Z K)
    (s p m q : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m) (hp : p+3 ≤ m) (hq : q+1 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ N i, k ≤ N → ∀ S : Scene C.path.levels i (p+1),
      Realized K N i k (p+1) (Lis.sun G u) S →
      (∀ j, k ≤ j → j ≤ N →
        let Q := C.path.rep N i j
        let β := C.path.levels.clock.hatBeta j
        let w := Mosaic.vol β
        let g := Heath.Stock.cue Q.beta
        JetTab (Measuring.chart _ G) (Mosaic.αm β) s w (Metric.closedBall 0 w)
          (Aqua.film Q (S.Poly j) g p) q (g^((p:ℝ)+1-η))) ∧
      ∀ j, k ≤ j → j < N →
        |Heath.Stock.cue (C.path.rep N i j).beta / Heath.Stock.cue (C.path.rep N i (j+1)).beta -
          Bakery.taste (p+1) (S.action j) (Heath.Stock.cue (C.path.rep N i j).beta)| ≤
          Mosaic.goalP (C.path.levels.clock.hatBeta j) (p+1) := by
  have high := Multi.Wage.hat_tend hG C.path.levels
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp ((Alto.broad.comp high).eventually_ge_atTop 32)
  obtain ⟨k₁,h₁⟩ := eventually_atTop.mp (high.eventually_ge_atTop 1)
  obtain ⟨k₂,h₂⟩ := eventually_atTop.mp (high.eventually (geometry_absorbed p q hη))
  filter_upwards [D.purse s (p+1) m hs hm hp,eventually_ge_atTop k₀,eventually_ge_atTop k₁,eventually_ge_atTop k₂] with k buy hk₀ hk₁ hk₂
  intro N i hkN S hS
  obtain ⟨tickets,reset,wedges⟩ := (buy N i hkN).2 S hS
  refine ⟨?_,reset⟩
  intro j hkj hjN
  let Q := C.path.rep N i j
  let β := C.path.levels.clock.hatBeta j
  let w := Mosaic.vol β
  let g := Heath.Stock.cue Q.beta
  have H : 32 ≤ Mosaic.hatW β := h₀ j (hk₀.trans hkj)
  have hβ : 1 ≤ β := h₁ j (hk₁.trans hkj)
  have hW : 0 < Mosaic.hatW β := by linarith
  have hw : 0 < w := div_pos hW (by norm_num)
  have ha : 0 ≤ Mosaic.αm β := zpow_nonneg hW.le _
  have hab : Mosaic.αm β ≤ Alto.candles C.path.levels j := by
    change (Mosaic.hatW β)^(-(3:ℤ)) ≤ 1/(Mosaic.hatW β)^2
    rw [zpow_neg,one_div]
    change ((Mosaic.hatW β)^(3:ℕ))⁻¹ ≤ ((Mosaic.hatW β)^(2:ℕ))⁻¹
    apply inv_anti₀ (sq_pos_of_pos hW)
    exact pow_le_pow_right₀ (by linarith) (by decide)
  have betas := (physical.represents N i j hjN).band
  have pos : 0 < Q.beta := (half_pos (zero_lt_one.trans_le hβ)).trans_le betas.1
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr pos)
  have budget := envelope_reference_price hβ pos betas.2 p
  rw [mul_pow] at budget
  have T := tickets j hkj hjN
  have W := (wedges j hkj hjN).shares (p+1) le_rfl
  have degree := ((hS.budget j hjN hkj).1.plane.profile (p+1) le_rfl)
  have J := JetTab.levelAll hw ha T.grown T.rangeP hm le_rfl q (by omega)
  have full := truncated_vacuum_envelope Q (S.Poly j) hg.le ha hab hw
    (show 1 ≤ Mosaic.hatW β by linarith) hq J
    (fun x hx => (T.grown x hx).of_le (by exact_mod_cast Nat.le_succ m)) W (by simpa using degree)
  apply full.cast _ Set.Subset.rfl
  refine le_trans ?_ (h₂ j (hk₂.trans hkj) Q.beta betas.1)
  unfold vacuumGeometry
  change 5*Mosaic.goalP β (p+1) + g^(p+1)*(w^(q+1)*_) ≤ g^(p+1)*(5*2^(p+1)+w^(q+1)*_)
  dsimp only [g,β,w,Alto.hat,Mosaic.hatW] at *
  nlinarith only [budget]

end YM.Integration.FVA1Physical.Round2
