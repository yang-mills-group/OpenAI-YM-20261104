import YM.Integration.FVA1Physical.Round2.VacuumTruncation

/-! A uniform physical-coupling price for the regular vacuum discrepancy on
the calibrated chart. The only geometry factor is an explicit polynomial in
the logarithm of the reference inverse coupling, independent of volume. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk MSbar.CrossH
open Filter RG Wilson Precision MSbar.Midpoint PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology

private theorem reference_price {β γ : ℝ} (hβ : 1 ≤ β) (hγ : 0 < γ) (h : γ ≤ 2*β) (p : ℕ) :
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

def vacuumGeometry (β : ℝ) (p q : ℕ) : ℝ :=
    5*2^(p+1) + (Mosaic.vol β)^(q+1) *
      (Alto.purse Alto.Dean (Mosaic.hatW β) (p+1) * (1+Mosaic.vol β)^(p+3))

/-- Choose the extra order before the initial cutoff, period, and step.
On the one realized scene the complete weighted row of every requested
derivative has the physical power g^(p+1) with explicit geometry cost. -/
theorem physical_vacuum_rate {G : Gauge} {C : Family G} {Z : Horizon C.path.levels}
    {u : G.ColorIndex} {O : ChartRatio G} {K : Kin Z O} (hG : G.Simple)
    (physical : C.path.Selected) (D : Docket C u O Z K)
    (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m) (hp : p+3 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ N i, k ≤ N → ∃ S : Scene C.path.levels i (p+1),
      Realized K N i k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → j ≤ N →
        let Q := C.path.rep N i j
        let β := C.path.levels.clock.hatBeta j
        let w := Mosaic.vol β
        let g := Heath.Stock.cue Q.beta
        ∀ (q : ℕ), q+1 ≤ m → ∀ x ∈ Metric.closedBall 0 w, ∀ v,
          w^(q+1)*regularRow (Measuring.chart _ G) (Mosaic.αm β) s q (Aqua.film Q (S.Poly j) g p) x v ≤
            g^(p+1)*vacuumGeometry β p q := by
  have high := Multi.Wage.hat_tend hG C.path.levels
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp ((Alto.broad.comp high).eventually_ge_atTop 32)
  obtain ⟨k₁,h₁⟩ := eventually_atTop.mp (high.eventually_ge_atTop 1)
  filter_upwards [D.purse s (p+1) m hs hm hp,eventually_ge_atTop k₀,eventually_ge_atTop k₁] with k buy hk₀ hk₁
  intro N i hkN
  obtain ⟨⟨S,hS⟩,covers⟩ := buy N i hkN
  obtain ⟨tickets,_,wedges⟩ := covers S hS
  refine ⟨S,hS,?_⟩
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
  have budget := reference_price hβ pos betas.2 p
  rw [mul_pow] at budget
  have T := tickets j hkj hjN
  have W := (wedges j hkj hjN).shares (p+1) le_rfl
  have degree := ((hS.budget j hjN hkj).1.plane.profile (p+1) le_rfl)
  dsimp only
  intro q hq x hx v
  have J := JetTab.levelAll hw ha T.grown T.rangeP hm le_rfl q (by omega)
  have row := film_row_truncate Q (S.Poly j) x v hg.le ha hab hw (show 1 ≤ Mosaic.hatW β by linarith)
    hq hx J ((T.grown _ hx).of_le (by exact_mod_cast Nat.le_succ m)) W (by simpa using degree)
  calc
    _ ≤ w^(q+1) * ((5*Mosaic.goalP β (p+1))/w^(q+1) +
        g^(p+1)*(Alto.purse Alto.Dean (Mosaic.hatW β) (p+1)*(1+w)^(p+3))) :=
      mul_le_mul_of_nonneg_left row (pow_nonneg hw.le _)
    _ = 5*Mosaic.goalP β (p+1) + g^(p+1)*(w^(q+1)*
        (Alto.purse Alto.Dean (Mosaic.hatW β) (p+1)*(1+w)^(p+3))) := by
      rw [mul_add,mul_div_cancel₀ _ (pow_pos hw _).ne']; ring
    _ ≤ _ := by
      unfold vacuumGeometry
      dsimp only [w,g] at *
      nlinarith only [budget]

end YM.Integration.FVA1Physical.Round2
