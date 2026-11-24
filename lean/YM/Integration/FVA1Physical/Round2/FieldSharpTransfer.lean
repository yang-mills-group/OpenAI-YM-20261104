import YM.Integration.FVA1Physical.Round2.FieldReadingTransfer
import YM.Integration.FVA1Physical.Round2.FieldOrderPurchase
import YM.Integration.FVA1Physical.Round2.FieldSharpClock

/-! Sharp physical-coupling comparison for a bounded mixed field once the
native conditional comparison and the omitted coefficient prices are supplied.
Both local and bulk series use the same regulator, nonflat stationary
background, interacting action and conditional normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool MSbar MSbar.Duel MSbar.Lis MSbar.Wave
open MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Mosaic MSbar.Bulk
open MSbar.Bakery MSbar.Whisk MSbar.Cacao MSbar.Rolling MSbar.Lapaz MSbar.Bakery.Film
open Push.Uniform YM.Integration.FVA1Physical.Wilson Next.SectorChange
open scoped Classical Topology
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

theorem mixed_field_sharp_transfer (V : Voice G) (clear : Clear G V) (χ : ChartRatio G)
    (hχ : LocalRatio χ) (simple : G.Simple) (H H' : RG.Stage) (P : Patch) (K : KernelChoices)
    (branch : P.Branches K G) (p s L : ℕ) (part : Bool) {D η : ℝ}
    (hD : 0 ≤ D) (hη : 0 < η) (hp : η < (p:ℝ)+1) :
    ∀ᶠ x : ℝ in atTop, ∀ (A : Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x; let g:=A.fClock; let n:=p+2
      Kind A.T → Expanse A.T 1 n → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s n →
      ∀ (Z : Positions (Primary A.c G)) (b : Site A.f) (o : ι → Site A.f), ‖Z‖ ≤ D →
        (∀ i : Slice J, separation b (legs J o i).1 ≤ L*closeN y) →
      let src:=jointFieldBank J A o part; let φ:=fun U=>look part (tally J o U)
      (∀ i, p < i → i ≤ n → |PowerSeries.coeff i (bulkColumn A χ (g•Z) src n)| ≤ y^(η/8)) →
      (∀ (pal : Palisade) (U : Config G A.f), U∈A.regionX y b Z V pal →
        |A.modelP y b Z pal V φ U - taste n (innerColumn A χ V y (g•Z) b U src n) g| ≤ y^(pawn n)) →
      |expect A.S A.pre (Rolling.postcard G A.c g Z) φ - taste p (bulkColumn A χ (g•Z) src p) g|
        ≤ g^((p:ℝ)+1-η) := by
  let n:=p+2
  let M:ℝ:=2*(n+1:ℕ)+10*stencilBound J
  have hM : 0≤M := by dsimp only [M];positivity [stencilBound_pos J]
  obtain ⟨pal,offer⟩ := purchased_chart_chance V clear simple H H' P K branch hD 0
  obtain ⟨_,_,seats⟩ := waiting pal H H' V χ hχ clear P 3 0
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [field_reading_transfer J V clear χ hχ simple H H' P K branch n s n L
      (by dsimp only [n];omega) part hD,offer,seats,rise.eventually_ge_atTop 2,
    rise.eventually (field_sharp_clock p M hM hη hp)] with x transfer purchase seat high price
  intro A patch kernel season y g _ kind plane wedge Z b o hZ near src φ caps point
  have pc:=season.case_
  rw [patch] at pc
  have one : (1:ℝ) ≤ A.pre.beta := by linarith only [pc.beta,high]
  have hy : 0 < y := by dsimp only [y];linarith only [high]
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le one))
  have gs : g ≤ 1 := inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt one)
  have scaled : ‖g • Z‖ ≤ g*D := by rw [norm_smul,Real.norm_of_nonneg gp.le];gcongr
  obtain ⟨grant,paid,_,_⟩:=purchase A patch kernel season (g•Z) b scaled
  obtain ⟨_,suite⟩:=seat.enter _ _ patch season (boxX y b) (boxY y b) A.F (g•Z) A.v grant
    (by rw [patch];exact paid.first)
  have tail := price_after_truncating (bulkColumn A χ (g•Z) src n) (bulkColumn A χ (g•Z) src p)
    p 2 gp.le gs (fun i hi=>owes_prefix _ suite.positivity.inv _ _ (Rolling.well _ _ _ _ kind) _ hi (by dsimp [n];omega)) caps
  have seed:=transfer A patch kernel season kind plane wedge Z b o hZ near (fun _=>0) (fun _=>0)
    (y^(pawn n)) (Real.rpow_nonneg hy.le _) (fun U hU=>by
      rw [field_local_inner J A V χ y b U Z n _ _ o part suite.positivity kind gp.ne']
      exact point pal U hU)
  have band : lensT y g := ever hy pc.beta pc.upper
  exact ((abs_sub_le _ _ _).trans (add_le_add seed tail)).trans (price g band)

end YM.Integration.FVA1Physical.Round2.Curvature
