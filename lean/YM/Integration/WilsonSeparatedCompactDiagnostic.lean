import YM.Integration.WilsonSeparatedProfileGrid
import YM.Integration.WilsonMacroscopicDisplacement

/-! The original signed full physical moment on an exact compact profile
and on a single character-admissible rounded version of that profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedCompactDiagnostic
open Function Filter Finset Set Metric MeasureTheory Lattice Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Frontier6.Road Trace.Pilot SharedIntrinsicWilsonGrid
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ}
    (source : FundedOriginalProperties.{u} hG b W) (pace : WilsonWindowReportingPace.Slow R.kit) {H:ℕ} (hH:0<H)
    (F : Final R.family f V) (fac : Facilities R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → tower V) (lead : Leading F J)
    {A : (Bel R.family.book).Hierarchy} (paid : ∀ d : ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) d)
    {n:ℕ} (d:Caps n) {N p D:ℕ} (P : Plan R.family D N p) {K : Set (Points n)} (compact : IsCompact K)
    (sep : K ⊆ conf n) {g : ℝ→ℝ} (hg : Coupling G g) {θ:ℝ} (θp:0<θ) (fit : 1+θ<P.c) :
    ∃ L M η:ℝ, 0≤L ∧ 0<η ∧ ∀ᶠ r in trail, ∀ X∈K,
      let x := WilsonSeparatedProfileGrid.sites R.family.S (P.j r) r X
      let y := R.family.S.gridPoint (P.j r) ∘ x
      WithinRoom r M η y 0 ∧ Screen y ∧ ∀ q : Viewers F, ∀ v:(i:Fin n)→(Bel R.family.book).Field (d i),
        ‖Orbits.moment (spectator F q) (posed r X) (Frame.born J r v)-
          Orbits.moment (spectator F q) y (Frame.born J r v)‖ ≤ L*r^θ*∏ i,‖v i‖ := by
  let empty (z:Empty) : V.Tag := Short.extra (z:=z)
  let w := voices empty
  have clear : ClearOf 0 Short.gapPos 1 := by constructor <;> intro i <;> cases i
  obtain ⟨L,a,nL,ap,slopes⟩ := WilsonMacroscopicDisplacement.original hG W source pace hH F fac Q J lead paid d w
    compact sep zero_lt_one hg
  obtain ⟨t,tp,stay⟩ := compact.exists_cthickening_subset_open (conf_open n) sep
  obtain ⟨M,η,_,ηp,valid⟩ := RG17.roomCosts compact.cthickening stay
  have soon := ((PhysMS.length_rate.rpow θ).tends (by linarith only [θp]) PhysMS.to_log_zoom).eventually_lt_const (lt_min ap tp)
  refine ⟨2*L,M,η,by positivity,ηp,?_⟩
  filter_upwards [slopes,WilsonSeparatedProfileGrid.fine P fit (n:=n),soon,PhysMS.length_rate.pos]
    with r slope rounding small rp X hx x y
  change 0<r at rp
  let X' := WilsonSeparatedProfileGrid.shape R.family.S (P.j r) r X
  have dist : ‖X'-X‖ ≤ r^θ := rounding X
  have h' : X'∈cthickening t K := mem_cthickening_of_dist_le X' X t K hx (by
    rw [dist_eq_norm]; exact dist.trans (small.le.trans (min_le_right ..)))
  have eq : posed r X'=y := WilsonSeparatedProfileGrid.at_shape _ _ rp X
  refine ⟨eq ▸ valid r rp X' h',WilsonSeparatedProfileGrid.screen R.family.S (P.j r) r X,?_⟩
  intro q v
  let ins := Frame.born J r v
  have price := slope X hx X' (dist.trans (small.le.trans (min_le_left ..))) Short.gapPos clear q v
  have a0 : whole (spectator F q) (posed r X) ins Short.gapPos w = Orbits.moment (spectator F q) (posed r X) ins :=
    Short.tagged F (Orbits.tags ins) (posed r X) q (Work.A05.smul_conf rp (sep hx))
  have a1 : whole (spectator F q) (posed r X') ins Short.gapPos w = Orbits.moment (spectator F q) (posed r X') ins :=
    Short.tagged F (Orbits.tags ins) (posed r X') q (Work.A05.smul_conf rp (stay h'))
  have vacant : upon (spectator F q) 0 0 Short.gapPos w (V.unit 0)=1 := Short.vacuum F q 0 0 empty
  change ‖whole (spectator F q) (posed r X') ins Short.gapPos w-whole (spectator F q) (posed r X) ins Short.gapPos w‖ ≤
    L*(1+‖upon (spectator F q) 0 0 Short.gapPos w (V.unit 0)‖)*(∏ i,‖v i‖)*‖X'-X‖ at price
  rw [a0,a1,eq,vacant,norm_one,norm_sub_rev] at price
  apply price.trans
  have nonnegative : 0≤L*(1+1)*(∏ i,‖v i‖) :=
    mul_nonneg (mul_nonneg nL (by norm_num)) (Finset.prod_nonneg fun i _=>norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left dist nonnegative).trans_eq (by ring)

end YM.Integration.WilsonSeparatedCompactDiagnostic
