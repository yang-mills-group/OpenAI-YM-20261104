import YM.Integration.FVA1Physical.Round2.StencilExteriorTests
import YM.Integration.FVA1Physical.Wilson.FluctuationColumns
import YM.Integration.FVA1Physical.Wilson.FluctuationExterior

/-! From a good-fibre field estimate to the unconditioned physical mixed
reading and the exterior-free formal Wilson polynomial at a measured step.
The only local price passed in is the cost of the conditional computation.
Both exterior transfers are purchased independently. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool MSbar MSbar.Duel MSbar.Lis MSbar.Wave
open MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Mosaic MSbar.Bulk
open MSbar.Bakery MSbar.Whisk MSbar.Cacao MSbar.Rolling MSbar.Lapaz MSbar.Bakery.Film
open Push.Uniform YM.Integration.FVA1Physical.Wilson Next.SectorChange
open scoped Classical Topology
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

theorem fluctuation_fields (V : Voice G) (clear : Clear G V) (χ : ChartRatio G)
    (hχ : LocalRatio χ) (simple : G.Simple) (H H' : RG.Stage) (P : Patch)
    (K : KernelChoices) (branch : P.Branches K G) (p s q L : ℕ) (part : Bool)
    {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season V H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖ ≤ D*room (tip G P.L x) →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ (o : ι→Site A.f), (∀ j:Slice J, separation b (legs J o j).1 ≤ L*closeN y) →
      let src:=jointFieldBank J A o part
      ∀ U∈hotel A.F (boxX y b) (boxY y b) V (represent (tint G (Exterior.Body 1 A.c) z))
        (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y),
      ∀ i ≤ p, |PowerSeries.coeff i (bulkColumn A χ z src p) -
        PowerSeries.coeff i (innerColumn A χ V y z b U src p)| ≤ y^(-(q:ℝ)) := by
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [fluctuation_columns V clear χ hχ simple H H' P K branch p s (p+2) q le_rfl hD,
    rise.eventually (field_vault_subpower J p s (p+2) L part (ε:=1) zero_lt_one)] with x offer bank
  intro A z b patch kernel season hz y kind plane wedge o near src U live i hi
  apply offer A z b patch kernel season hz kind plane wedge src _ U live i hi
  intro n hn
  obtain ⟨v,deg⟩:=bank A o b near n hn
  simpa only [Real.rpow_one] using And.intro v (deg.trans (by omega : n≤p+2))

theorem fluctuation_field_reading (V : Voice G) (clear : Clear G V) (χ : ChartRatio G)
    (hχ : LocalRatio χ) (simple : G.Simple) (H H' : RG.Stage) (P : Patch) (K : KernelChoices)
    (branch : P.Branches K G) (p s q L : ℕ) (hq : 0 < q) (part : Bool) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ x : ℝ in atTop, ∀ (A : Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x; let g:=A.fClock
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ (Z : Positions (Primary A.c G)) (b : Site A.f) (o : ι → Site A.f), ‖g • Z‖ ≤ D*room y →
        (∀ i : Slice J, separation b (legs J o i).1 ≤ L*closeN y) →
      let O:=represent (tint G (Exterior.Body 1 A.c) (g • Z))
      let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) (g • Z)
      let X:=boxX y b; let Y:=boxY y b; let area:=hotel A.F X Y V O μ (pillow y) (room y)
      let r:=woolModel A.F X V A.pre Y A.v O μ (pillow y) (room y)
      let φ:=fun U => look part (tally J o U); let src:=jointFieldBank J A o part
      ∀ (cutoff : ℝ→ℝ) (color : Site A.f → G.Color) (ε : ℝ), 0 ≤ ε →
        (∀ U ∈ area, |Rota.resample A.F (board A.F X) r area φ U -
          localW A.F A.pre A.v V χ X Y U g Z A.T p cutoff color src| ≤ ε) →
        |expect A.S A.pre O φ - taste p (bulkColumn A χ (g • Z) src p) g| ≤
          2*ε+(2*(p+1:ℕ)+10*stencilBound J)*y^(-(q:ℝ)) := by
  obtain ⟨pal,offer⟩ := purchased_fluctuation_chance V clear simple H H' P K branch hD 0
  obtain ⟨_,_,seats⟩ := waiting pal H H' V χ hχ clear P 3 0
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [fluctuation_field_exterior V clear simple H H' P K branch hD (Nat.cast_pos.mpr hq),
    fluctuation_fields J V clear χ hχ simple H H' P K branch p s q L part hD, offer,seats,
    rise.eventually_ge_atTop 2,rise.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop L)]
    with x exterior rows purchase seat high wide
  intro A patch kernel season y g kind plane wedge Z b o hZ near O μ X Y area r φ src clamp color ε hε point
  have pc:=season.case_
  rw [patch] at pc
  have one : (1:ℝ) ≤ A.pre.beta := by linarith only [pc.beta,high]
  have gpos : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le one))
  have gsmall : g ≤ 1 := inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt one)
  obtain ⟨grant,paid,_,_⟩:=purchase A patch kernel season (g•Z) b hZ
  obtain ⟨_,suite⟩:=seat.enter _ _ patch season X Y A.F (g•Z) A.v grant (by rw [patch];exact paid.first)
  have covered (i : Slice J) : separation b (legs J o i).1 ≤ spotN y :=
    (near i).trans (by unfold closeN spotN; rw [pow_succ' (radiusB y) 3]; exact Nat.mul_le_mul_right _ wide)
  let M:=stencilBound J
  let W:=taste p (bulkColumn A χ (g•Z) src p) g
  let a:=y^(-(q:ℝ))
  let v:=ε+(p+1:ℕ)*a
  have ha : 0 ≤ a:=Real.rpow_nonneg (by dsimp only [y];linarith only [high]) _
  have hv : 0 ≤ v:=add_nonneg hε (mul_nonneg (Nat.cast_nonneg _) ha)
  have hM : 0 < M:=stencilBound_pos J
  have localφ := collar_stencil_local J A.S A.F o part b y covered
  have unitφ : GaugeLocal A.S (youth A.F Y) (M⁻¹ • φ) :=
    ⟨(Envelope.const _).mul localφ.currency,fun k hk U=>congrArg (M⁻¹*·) (localφ.turn k hk U),
      fun U U' same=>congrArg (M⁻¹*·) (localφ.located U U' same)⟩
  have capφ (U) : |(M⁻¹ • φ) U| ≤ 1 := by
    change |M⁻¹ * φ U| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr hM)]
    exact (inv_mul_le_iff₀ hM).mpr ((stencil_bounded J o part U).trans_eq (mul_one M).symm)
  have localPrice (U) (keep : U∈area) : |Rota.resample A.F (board A.F X) r area φ U-W| ≤ v := by
    have lev:=point U keep
    rw [field_local_inner J A V χ y b U Z p clamp color o part suite.positivity kind gpos.ne'] at lev
    have cs:=rows A (g•Z) b patch kernel season hZ kind plane wedge o near U keep
    exact (abs_sub_le _ _ _).trans (add_le_add lev ((abs_sub_comm _ _).le.trans
      (finite_taste_transfer p _ _ gpos.le gsmall cs)))
  have uncond:=exterior A patch kernel season (g•Z) b hZ (M⁻¹ • φ) unitφ capφ
    (M⁻¹*W) (M⁻¹*v) (mul_nonneg (inv_nonneg.mpr hM.le) hv) (fun U keep=>by
      rw [resample_vscale]
      change |M⁻¹ * _ - M⁻¹*W| ≤ _
      rw [←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hM)]
      exact mul_le_mul_of_nonneg_left (localPrice U keep) (inv_nonneg.mpr hM.le))
  rw [e_mul,←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hM)] at uncond
  have final := (inv_mul_le_iff₀ hM).mp uncond
  apply final.trans_eq
  change M * (2*(M⁻¹*v)+10*a)=2*ε+(2*(p+1:ℕ)+10*M)*a
  dsimp only [v]
  field_simp [hM.ne']
  push_cast
  ring

end YM.Integration.FVA1Physical.Round2.Curvature

