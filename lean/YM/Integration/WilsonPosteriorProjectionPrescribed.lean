import YM.Integration.WilsonPosteriorProjectionCommonCensus
import YM.Integration.WilsonPosteriorProjectionTestRadial
import YM.Integration.WilsonPosteriorProjectionRootedInlet
import YM.Integration.WilsonPosteriorProjectionThermalWindow
import YM.Integration.WilsonPosteriorProjectionGerm
import YM.Integration.WilsonPosteriorProjectionBank

/-! The original nonlinear macroscopic readout of the *true* fresh finite
stencil, compared to the *independent* emitted bank on the identical physical
scene. The complete torus and angular chain rule are taken before pricing. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionPrescribed

open Set Function Filter Finset MeasureTheory Lattice RG YM.Wilson Precision Tree Exterior Push.Uniform
open Source Labels Next.Foundations PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Midpoint MSbar.Cacao MSbar.Bakery.Film
open MSbar.Whisk MSbar.Lis MSbar.Rolling MSbar.Bulk MSbar.Mosaic MSbar.CrossH
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature FVA1Physical.Marked RG01.Kernel
open WilsonPosteriorProjectionPinned WilsonPosteriorProjectionCommonRooted WilsonPosteriorProjectionCommonCensus
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {I : Type} [Fintype I] {d₀ : ℕ}

def AtRate (a : I → CoverLabel G d₀) (R : Run G) (u : G.ColorIndex)
    (H : Hol G) (jet : Jet G) (d p K L radius : ℕ)
    (admit : ℕ→ℕ→ℕ→ℝ→Prop) (fare : ℝ→ℝ→ℝ) : Prop :=
  ∃ C : ℝ, 0≤C ∧ ∀ᶠ k : ℕ in atTop, ∀ N n, k≤N →
    (∃ S : Scene R.family.path.levels n (audit p K+2),
      Realized R.alloy.B.kin N n k (audit p K+2) (Lis.sun G u) S) ∧
    ∀ (S : Scene R.family.path.levels n (audit p K+2))
      (scene : Realized R.alloy.B.kin N n k (audit p K+2) (Lis.sun G u) S)
      (j : ℕ) (kj : k≤j) (jN : j<N),
      let F := (scene.step j jN kj).choose
      let v := (scene.step j jN kj).choose_spec.choose
      let A := sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
      let y := R.family.path.levels.clock.hatBeta (j+1)
      let g := A.fClock
      S.Poly j=A.Zpost R.metals.O ∧ ∀ (b : Site A.c) (o : I→Site A.f),
        (∀ i, separation (o i-A.S.ratio.embed b) 0 ≤ radius) →
        (∀ t : Slice (freshLamps a), separation (A.S.ratio.embed b) (legs (freshLamps a) o t).1 ≤ L*closeN y) →
        ∀ (part : Bool) (θ : ℝ), 0≤θ → θ≤1 → admit N n j θ →
        let f := fun W => expect A.S A.pre W (fun U => look part (tally (freshLamps a) o U))
        let bank := clockReading p g (emittedRows A R.metals.O (enterRows A (stencilInlet (freshLamps a) o part)) p)
        |iteratedDeriv K (f ∘ H.testLinks d b (θ • jet)) 0 -
         iteratedDeriv K (bank ∘ WilsonPosteriorProjectionTestGrowth.curve H d b (θ • jet) g) 0| ≤
          C*fare g θ

abbrev Actual (a : I → CoverLabel G d₀) (R : Run G) (u : G.ColorIndex)
    (H : Hol G) (jet : Jet G) (d p K L radius : ℕ) (η : ℝ) :=
  AtRate a R u H jet d p K L radius (fun _ _ _ _ => True)
    (fun g θ => (max 1 (g⁻¹*θ))^K*g^((p:ℝ)+1-η))

abbrev Thermal (a : I → CoverLabel G d₀) (R : Run G) (u : G.ColorIndex)
    (H : Hol G) (jet : Jet G) (d p K L radius : ℕ) (η : ℝ) :=
  AtRate a R u H jet d p K L radius (fun N n j θ => θ=(R.family.path.rep N n j).p.threshold)
    (fun g _ => g^((p:ℝ)+1-η))

theorem priced (a : I → CoverLabel G d₀) (R : Run G) (u : G.ColorIndex) (hG : G.Simple)
    (V : Voice G) (cle : Clear G V) (inputs : PinnedReadings (freshLamps a) R u)
    (rows : PinnedEmissions (freshLamps a) R u) (cash : Late R (rootedFieldMenu a))
    (H : Hol G) (jet : Jet G) (d p K L radius : ℕ) (K0 : 0<K) {η : ℝ} (hη : 0<η) :
    Actual a R u H jet d p K L radius η := by
  let s := 6+K
  have weight : 6 ≤ s := Nat.le_add_right ..
  obtain ⟨C,C0,read⟩ := WilsonPosteriorProjectionTestRadial.ratio H d K jet K0 s (Nat.le_add_left ..)
  let stage := fun (q k : ℕ) => AtStage a R u p q s L radius 0 η (audit p K) k
  have bought (q : ℕ) (hq : 0<q) (qK : q≤K) : ∀ᶠ k : ℕ in atTop, stage q k :=
    each a R u hG V cle inputs rows cash p K q s L radius hq qK weight le_rfl hη
  have all : ∀ᶠ k : ℕ in atTop, ∀ i : Fin K, stage (i.val+1) k :=
    Filter.eventually_all.mpr fun i => bought (i.val+1) (Nat.succ_pos _) i.isLt
  obtain ⟨floor,large⟩ := eventually_atTop.mp ((Multi.Wage.hat_tend hG R.family.path.levels).eventually_ge_atTop (2:ℝ))
  refine ⟨C,C0,?_⟩
  filter_upwards [bought K K0 le_rfl,all,eventually_ge_atTop floor] with k high grades late N n kn
  obtain ⟨existsScene,atTopRank⟩ := high N n kn
  refine ⟨existsScene,?_⟩
  intro S scene j kj jN F v A y g
  refine ⟨(atTopRank S scene j kj jN).1,?_⟩
  intro b o near legsClose part θ hθ θ1 _ groupFn bank
  let J := freshLamps a
  let obs := fun U => look part (tally J o U)
  let x := R.family.path.levels.clock.hatBeta j
  have y2 : 2≤y := large (j+1) (late.trans (kj.trans (Nat.le_succ j)))
  have beta := (R.T.choice.represents N n (j+1) jN).band
  obtain ⟨hg,_,_,_⟩ := WilsonPosteriorProjectionBooking.cooling y A.pre.beta 0 y2 beta.1
  have fineBound : Bounded (prior G A.f) (fun (_ : A.S.Choices) U => ((obs U : ℝ) : ℂ)) (stencilBound J) := by
    refine ⟨fun _ => (Complex.continuous_ofReal.comp ((look part).continuous.comp
      (Spool.tally_cont J o))).aestronglyMeasurable, ?_⟩
    intro _ U
    simpa only [Complex.norm_real,Real.norm_eq_abs] using (stencil_bounded J o part U)
  have measured := WilsonPosteriorProjectionGerm.regular R.family.path R.T.choice
    (N:=N) (n:=n) (m:=j) jN obs g K fineBound (stencilBound_pos J).le
  have formal := (WilsonPosteriorProjectionBank.regular p g
    (emittedRows A R.metals.O (enterRows A (stencilInlet J o part)) p) K).contDiffAt (x:=0)
  rw [←mul_assoc]
  apply read A.c b g θ (g^((p:ℝ)+1-η)) hg hθ θ1 (Real.rpow_nonneg hg.le _)
    (fun q => rootedChartWidth q x) groupFn bank measured formal
  intro q hq qK
  have logs : 0 < Real.log x := Real.log_pos (R.family.path.levels.fits.delayed j)
  refine ⟨by unfold rootedChartWidth αm hatW Alto.flurry; positivity, ?_⟩
  let i : Fin K := ⟨q-1,by omega⟩
  have qi : i.val+1=q := by dsimp [i]; omega
  have bill := ((grades i N n kn).2 S scene j kj jN).2 b o near legsClose part
    (fun _ => 0) (fun _ => by simp)
  rw [qi] at bill
  change fieldDistance (Measuring.chart A.c G) b (rootedChartWidth q x) s q
    (fun _ => 0) (groupFn ∘ postcard G A.c g) bank ≤ _
  change fieldDistance _ _ _ _ _ _ _ (clockReading p A.fClock
    (emittedRows A R.metals.O (enterRows A (stencilInlet (freshLamps a) o part)) p)) ≤ _
  rw [WilsonPosteriorProjectionRootedInlet.clock]
  exact bill

/-- The zero angular rank is the value at the identity, read on the original
field-word buyer's own audit. The fresh nonconstant source and independent
formal denominator remain the same as at positive reported ranks. -/
theorem value (a : I → CoverLabel G d₀) (R : Run G) (u : G.ColorIndex) (hG : G.Simple)
    (inputs : PinnedReadings (freshLamps a) R u) (rows : PinnedEmissions (freshLamps a) R u)
    (H : Hol G) (jet : Jet G) (d p L radius : ℕ) {η : ℝ} (hη : 0<η) :
    Thermal a R u H jet d p 0 L radius η := by
  have words := physical_field_words (freshLamps a) hG R u inputs rows p 0 6 L le_rfl 0 η le_rfl hη
  refine ⟨1,zero_le_one,?_⟩
  filter_upwards [words] with k received N n kn
  obtain ⟨existsScene,read⟩ := received N n kn
  refine ⟨existsScene,?_⟩
  intro S scene j kj jN F v A y g
  obtain ⟨same,point⟩ := read S scene j kj jN
  refine ⟨same,?_⟩
  intro b o _ near part θ _ _ _ groupFn bank
  have bill := point b 0 (by simp) o near part [] rfl
  change |groupFn (postcard G A.c g 0)-clue (renderedPolynomial
    (emittedRows A R.metals.O (jointFieldBank (freshLamps a) A o part) p) p g) 0| ≤
      g^((p:ℝ)+1-η) at bill
  have zero : postcard G A.c g 0=1 := by simp [postcard]
  have formal := congrFun (WilsonPosteriorProjectionRootedInlet.clock (freshLamps a) A R.metals.O p o part) 0
  change bank 0 = _ at formal
  rw [zero,←formal] at bill
  simpa only [iteratedDeriv_zero,comp_apply,Next.Foundations.test_one,WilsonPosteriorProjectionTestGrowth.center,one_mul]
    using bill

/-- At the actual reported coarse amplitude all angular factors are absorbed
by an arbitrary power loss on the *same* polynomial truncation p. -/
theorem thermal (a : I → CoverLabel G d₀) (R : Run G) (u : G.ColorIndex) (hG : G.Simple)
    (V : Voice G) (cle : Clear G V) (inputs : PinnedReadings (freshLamps a) R u)
    (rows : PinnedEmissions (freshLamps a) R u) (cash : Late R (rootedFieldMenu a))
    (window : Late R (WilsonPosteriorProjectionThermalWindow.changeFee G))
    (H : Hol G) (jet : Jet G) (d p K L radius : ℕ) (K0 : 0<K) {η : ℝ} (hη : 0<η) :
    Thermal a R u H jet d p K L radius η := by
  obtain ⟨C,C0,quotes⟩ := priced a R u hG V cle inputs rows cash H jet d p K L radius K0 (half_pos hη)
  have clock := WilsonPosteriorProjectionThermalWindow.reported R hG K (half_pos hη) window
  refine ⟨C,C0,?_⟩
  filter_upwards [quotes,clock] with k property gain N n kn
  obtain ⟨sceneExists,quotes⟩ := property N n kn
  refine ⟨sceneExists,?_⟩
  intro S scene j kj jN F v A y g
  obtain ⟨same,field⟩ := quotes S scene j kj jN
  refine ⟨same,?_⟩
  intro b o near legsClose part θ hθ θ1 stated groupFn bank
  have measured := field b o near legsClose part θ hθ θ1 trivial
  obtain ⟨g0,inside⟩ := gain j kj N n jN
  have buy : (max 1 (g⁻¹*θ))^K ≤ g^(-(η/2)) := by rw [stated]; exact inside
  apply measured.trans
  apply mul_le_mul_of_nonneg_left _ C0
  apply (mul_le_mul_of_nonneg_right buy (Real.rpow_nonneg g0.le _)).trans_eq
  change g^(-(η/2))*g^((p:ℝ)+1-η/2)=g^((p:ℝ)+1-η)
  have gPos : 0 < g := g0
  rw [←Real.rpow_add gPos]
  congr 1
  ring

end YM.Integration.WilsonPosteriorProjectionPrescribed
end

