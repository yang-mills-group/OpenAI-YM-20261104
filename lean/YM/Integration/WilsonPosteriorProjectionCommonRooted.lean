import YM.Integration.FVA1Physical.Round2.PurchasedRootedField
import YM.Integration.WilsonPosteriorProjectionCommonWords

/-! The authentic signed spatial field buyer at a fixed supplied audit
grade. This allows all ranks of a nonlinear observable to share one true
Gaussian bank, Haar law, forest, prior and scene. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionCommonRooted
open Function Filter Finset Lattice RG YM.Wilson Precision RG.Supply Input Org Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson Integration.FVA1Physical.Marked RGComparison.Core16 RGComparison.Core16.Spool
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Midpoint MSbar.Cacao MSbar.CrossH MSbar.Bakery.Film MSbar.Whisk
open MSbar.Rolling MSbar.Kelvin MSbar.Lis MSbar.Bulk MSbar.Mosaic Tree Pressure Push.Uniform Exterior
open scoped Classical Topology BigOperators ContDiff
open FVA1Physical.Round2.Curvature
variable {G : Gauge} {I : Type} [Fintype I] {d : ℕ} (a : I → CoverLabel G d)

def AtStage (R : PhysicalNext.Repeat.Legato.Run G) (u : G.ColorIndex)
    (p q s L radius : ℕ) (D η : ℝ) (m k : ℕ) : Prop :=
  let r := m+2
  ∀ N n, k ≤ N →
    (∃ S : Scene R.family.path.levels n r, Realized R.alloy.B.kin N n k r (Lis.sun G u) S) ∧
    ∀ (S : Scene R.family.path.levels n r) (scene : Realized R.alloy.B.kin N n k r (Lis.sun G u) S)
      (j : ℕ) (kj : k ≤ j) (jN : j < N),
      let F := (scene.step j jN kj).choose
      let v := (scene.step j jN kj).choose_spec.choose
      let A := sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
      let x := R.family.path.levels.clock.hatBeta j
      let y := R.family.path.levels.clock.hatBeta (j+1)
      S.Poly j=A.Zpost R.metals.O ∧
      ∀ (b : Site A.c) (o : I → Site A.f),
        (∀ i, separation (o i-A.S.ratio.embed b) 0 ≤ radius) →
        (∀ t : Slice (freshLamps a), separation (A.S.ratio.embed b) (legs (freshLamps a) o t).1 ≤ L*closeN y) →
        ∀ (part : Bool) (Z : List (Primary A.c G) → Positions (Primary A.c G)), (∀ l, ‖Z l‖ ≤ D) →
        let f := fun z => expect A.S A.pre (postcard G A.c A.fClock z) (fun U => look part (tally (freshLamps a) o U))
        let Q := renderedPolynomial (emittedRows A R.metals.O (jointFieldBank (freshLamps a) A o part) p) p A.fClock
        fieldDistance (Measuring.chart A.c G) b (rootedChartWidth q x) s q Z f (clue Q) ≤ A.fClock^((p:ℝ)+1-η)

def AtGrade (R : PhysicalNext.Repeat.Legato.Run G) (u : G.ColorIndex)
    (p q s L radius : ℕ) (D η : ℝ) (m : ℕ) : Prop :=
  ∀ᶠ k : ℕ in atTop, AtStage a R u p q s L radius D η m k

theorem atGrade (R : PhysicalNext.Repeat.Legato.Run G) (u : G.ColorIndex) (hG : G.Simple)
    (V : Voice G) (clear : Clear G V)
    (rows : PinnedEmissions (freshLamps a) R u) (p q s L radius m : ℕ) (pm : p+(p+8) ≤ m) (hq : 0 < q) (hs : 6 ≤ s)
    {D η : ℝ} (hD : 0 ≤ D) (hη : 0 < η)
    (words : WilsonPosteriorProjectionCommonWords.AtOrder (freshLamps a) R u (p+(p+8)) q L D 1 m)
    {γ : ℝ} (hγ : 0 < γ) (narrowPrice : γ ≤ rowExponent η)
    (purchase : LateThreshold R (chargeGate a q (s+s) radius hγ)) : AtGrade a R u p q s L radius D η m := by
  let J := freshLamps a
  let extra := p+8
  let P := p+extra
  let r := m+2
  let h := emittedDegree P
  let C := (1+D)^(h+1)
  have C0 : 0 ≤ C := pow_nonneg (by linarith only [hD]) _
  have pr : P ≤ r := pm.trans (Nat.le_add_right m 2)
  have hδ := (derivative_clock p 0 0 le_rfl hη).1
  have actual := purchased_current_charge R hG V clear a q (s+s) radius hq hγ hD purchase
  have scale := Multi.Wage.hat_tend hG R.family.path.levels
  obtain ⟨t,clock⟩ := eventually_atTop.mp (summed_field_clock p C C0 hη)
  obtain ⟨u₀,money⟩ := eventually_atTop.mp (derivative_clock p 0 0 le_rfl hη).2
  obtain ⟨K,late⟩ := eventually_atTop.mp (scale.eventually_ge_atTop (2*max 1 (max t u₀)))
  have radial := scale.eventually (field_kernel_subpower G q (rowExponent η) hδ)
  obtain ⟨S₀,rad⟩ := eventually_atTop.mp radial
  change ∀ᶠ k : ℕ in atTop, _
  filter_upwards [words,rows P r (s+s) h L pr (by omega) 0 (rowExponent η) le_rfl hδ,
    rows P r s h L pr hs 0 (rowExponent η) le_rfl hδ,actual,
    regular_field_domain hG R V clear D hD,eventually_ge_atTop K,eventually_ge_atTop S₀]
    with k step strong weak paid domain cut radcut N n kn
  obtain ⟨existsScene,reading⟩ := step N n kn
  refine ⟨existsScene,?_⟩
  intro S scene j kj jN F v A x y
  have entry := reading S scene j kj jN
  refine ⟨entry.1,?_⟩
  have je := kj.trans (Nat.le_succ j)
  let chain := RunFormalChain.fromRun R
  have good := R.T.choice.represents N n (j+1) jN
  have tr := (scene.budget (j+1) jN je).1
  have band : y/2 ≤ A.pre.beta := good.band.1
  have cutβ : max 1 (max t u₀) ≤ A.pre.beta := by
    have he := late (j+1) (cut.trans je)
    linarith only [he,band]
  have B1 : 1 ≤ A.pre.beta := (le_max_left ..).trans cutβ
  have gp : 0 < A.fClock := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le B1))
  have unit : A.fClock ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr B1)
  have hx : 1 ≤ x := (R.family.path.levels.fits.delayed j).le
  have xβ : x ≤ 2*A.pre.beta := by
    have xy : x ≤ y := WilsonBulk.Parapet.Agenda.hat_mobile R.family.path.levels hG (Nat.le_succ j)
    linarith only [xy,band]
  have size := (money A.pre.beta ((le_max_right ..).trans ((le_max_right ..).trans cutβ)) x hx xβ).1
  have log0 : 0 < Real.log x := Real.log_pos (R.family.path.levels.fits.delayed j)
  have radius0 : 0 < rootedChartWidth q x := by unfold rootedChartWidth αm hatW Alto.flurry; positivity
  have bw : ((q:ℝ)+2)*rootedChartWidth q x=αm x := by unfold rootedChartWidth; field_simp
  have narrow : rootedChartWidth q x ≤ αm x := by
    rw [←bw]
    exact le_mul_of_one_le_left radius0.le (by linarith only [Nat.cast_nonneg (α:=ℝ) q])
  have radialPaid : (fieldKernel G (rootedChartWidth q x))^q ≤ A.pre.beta :=
    (le_abs_self _).trans ((rad j (radcut.trans kj)).trans size)
  have branch := (R.family.path.levels.blocks j n).branches
  have pd : (mold A.pre A.F A.v).PosDef := by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [chain.clips N n (j+1) jN,chain.selected N n (j+1) jN]
    exact blueprint F v (chain.kin.path N (j+1)) _ branch tr.quiet (chain.post.price _) (chain.planned.gap N j n jN F)
  have plane : Expanse A.T 1 P := ⟨fun i hi => tr.plane.profile i (hi.trans pr)⟩
  intro b o foot near part Z inside f Q
  let src := jointFieldBank J A o part
  let PH := renderedPolynomial (emittedRows A R.metals.O src P) P A.fClock
  let g := A.fClock
  let τ := g^(p+4)
  have positive : 0 < τ := pow_pos gp _
  have smooth (l : List (Primary A.c G)) : ContDiffAt ℝ q f (Z l) := by
    let φ := fun U => look part (tally J o U)
    have env : Envelope φ := Lumen.Planet.havenreal ((look part).continuous.comp (Spool.tally_cont J o))
    have funds := reading_chart_order A.S A.pre φ branch (A.pre.envelope good.good)
      (SectorNext.Vacuum.strictly R.family.path R.T.choice N n (j+1) jN) env (stencil_bounded J o part)
      univ (ContinuousLinearMap.id ℝ (Positions (Primary A.c G))) ContinuousLinearMap.norm_id_le
      (fun _ e he => False.elim (he (mem_univ e))) g ((abs_of_pos gp).trans_le unit) (Z l)
      (domain N n j kj jN (Z l) (inside l)).1.le q
    exact (translate_through (f:=f) (z:=Z l) funds).smooth
  have point (l : List (Primary A.c G)) (hl : l.length=q) : |buoy f (Z l) l-buoy (clue PH) (Z l) l| ≤ g^P := by
    have bound := entry.2 b (Z l) (inside l) o near part l hl
    change |buoy (f-clue PH) (Z l) l| ≤ g^((P:ℝ)+1-1) at bound
    rwa [Cypress.remove q l (Z l) f (clue PH) (smooth l) (helm PH q).contDiffAt hl.le,add_sub_cancel_right,Real.rpow_natCast] at bound
  have result := raised_field_rooted A R.metals.O src tr.bond pd b p extra s q h f Z
    radius0 hD (pow_nonneg gp.le P) positive gp.le unit inside
    (emitted_degree_exact_order A R.metals.O J o part P tr.bond plane pd)
    (by rw [bw];exact (strong N n kn).2 S scene j kj jN b 0 (by simp) o near part)
    (fun i _ hi => Quote.cooled radius0.le narrow ((weak N n kn).2 S scene j kj jN b 0 (by simp) o near part i hi))
    point (M:=A.pre.beta) (by
      rw [bw]
      exact (paid N n j kj jN b o foot part Z inside).trans ((Real.rpow_le_rpow_of_exponent_le hx narrowPrice).trans size))
  apply result.trans
  apply (add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left radialPaid
    (div_nonneg (pow_nonneg gp.le _) positive.le))) (le_refl _)).trans
  exact clock A.pre.beta ((le_max_left ..).trans ((le_max_right ..).trans cutβ)) x hx xβ


end YM.Integration.WilsonPosteriorProjectionCommonRooted
end

