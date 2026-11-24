import YM.Integration.FVA1Physical.Round2.FieldOrderStability
import YM.Integration.FVA1Physical.Wilson.FieldRows

/-! Truncate a computed physical field to its requested order on the same
nonflat stationary point. Every omitted coefficient is paid by the rooted
field estimate. The threshold precedes the box, forest, positions and tests. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool MSbar MSbar.Duel MSbar.Lis MSbar.Wave
open MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Mosaic MSbar.Bulk
open MSbar.Bakery MSbar.Whisk MSbar.Cacao MSbar.Rolling MSbar.Lapaz MSbar.Bakery.Film
open Push.Uniform YM.Integration.FVA1Physical.Wilson Next.SectorChange
open scoped Classical Topology
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

theorem field_order_price (V : Voice G) (clear : Clear G V) (χ : ChartRatio G)
    (hχ : LocalRatio χ) (simple : G.Simple) (H H' : RG.Stage) (P : Patch) (K : KernelChoices)
    (branch : P.Branches K G) (p d s L : ℕ) (part : Bool) {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (A : Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x; let g:=A.fClock; let n:=p+d; let k:=n+1+n
      Kind A.T → Expanse A.T 1 k → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s k →
      ∀ (Z : Positions (Primary A.c G)) (b : Site A.f) (o : ι → Site A.f), ‖Z‖ ≤ D →
        (∀ i : Slice J, separation b (legs J o i).1 ≤ L*closeN y) →
      let src:=jointFieldBank J A o part
      |taste n (bulkColumn A χ (g • Z) src n) g - taste p (bulkColumn A χ (g • Z) src p) g| ≤
        (d:ℝ)*g^(p+1)*y^δ := by
  obtain ⟨pal,offer⟩ := purchased_chart_chance V clear simple H H' P K branch hD 0
  obtain ⟨_,_,seats⟩ := waiting pal H H' V χ hχ clear P 3 0
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [physical_field_rows J V clear χ hχ simple H H' P K branch (p+d) s 0 L part hD hδ,
    offer,seats,rise.eventually_ge_atTop 2] with x rows purchase seat high
  intro A patch kernel season y g n k kind plane wedge Z b o hZ near src
  have pc:=season.case_
  rw [patch] at pc
  have one : (1:ℝ) ≤ A.pre.beta := by linarith only [pc.beta,high]
  have gpos : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le one))
  have gsmall : g ≤ 1 := inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt one)
  have scaled : ‖g • Z‖ ≤ g*D := by rw [norm_smul,Real.norm_of_nonneg gpos.le];gcongr
  obtain ⟨grant,paid,_,_⟩:=purchase A patch kernel season (g•Z) b scaled
  obtain ⟨_,suite⟩:=seat.enter _ _ patch season (boxX y b) (boxY y b) A.F (g•Z) A.v grant
    (by rw [patch];exact paid.first)
  have ha : 0 ≤ αm y := by unfold αm hatW Alto.flurry; positivity
  apply price_after_truncating _ _ p d gpos.le gsmall
  · exact fun i hi=>owes_prefix _ suite.positivity.inv _ _ (Rolling.well _ _ _ _ kind) _ hi (by dsimp [n];omega)
  · intro i _ hi
    rw [normalizedRows_read]
    exact Bout.looks ha (rows A b patch kernel season kind plane wedge (g•Z) scaled o near i hi)

end YM.Integration.FVA1Physical.Round2.Curvature
