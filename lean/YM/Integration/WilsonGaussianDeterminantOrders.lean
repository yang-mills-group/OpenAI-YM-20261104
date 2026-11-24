import YM.Integration.WilsonGaussianDeterminantReportedMS
import YM.Integration.WilsonReportingDecoratedPaidWord

/-! At arbitrary fixed Taylor order and arbitrary marked derivative order the same prepared cash
pays the signed low word and the whole normalized Gaussian determinant in the physical coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantOrders
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Port RGLocalTaylor RGLocalTaylor.Insert RGLocalTaylor.Mayer
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Daisy.Charity.RG12
open WilsonRetainedMiniatureTaylor WilsonRetainedDecoratedWord
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {P:Teller G}
    {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W} {R:Rep G f}

open WilsonGaussianDeterminantRoster WilsonGaussianDeterminantFull PhysicalAffineScalarLogarithm
open RGLocalTaylor LocalTaylorR2.Pavilion

open WilsonGaussianDeterminantStage
open PhysicalNext PhysicalNext.Repeat.Legato PhysicalNext.JointLoad Heir Heir.Suite Push.PriceCompiler Supply Testing

def Due (χ : Chi) (H : Cash W s μ L Q o C T R) (p j : ℕ) (g ε : ℝ) : Prop :=
  (∀ i : Bond f, Sees H j (mode G L s) (mode G L s) χ
      (fun _ X _ => fullPair X i - seed X i - model p R X i) (ε*g^p) 1) ∧
  Sees H j (mode G L s) (mode G L s) χ
    (fun _ X _ => WilsonGaussianDeterminantVolume.scalar X - ∑ i, (seed X i + model p R X i))
    ((Fintype.card (Bond f):ℝ) * (ε*g^p)) 1


def Word (χ : Chi) (H : Cash W s μ L Q o C T R) (p : ℕ) (g ε : ℝ) : Prop :=
  ∃ w:Miniature _ _→ℝ,
    Sales (radiusB s) Q.relative Q.ε (sleeve S (radiusB s) Q.halo) w (fun _=>0) (ε*g^p) ∧
    ∀ (A:Team R) (team:Molecule S), A.signs S ⊆ team →
  ∀ (start:Start (team\A.signs S)) (M:ℕ) (u:Decors (team\A.signs S) M)
    (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K → X.manifest → X.χ=χ →
    Healthy (Pressure.temp s) (H.unionP team) X.V →
    let error z:=Mayer.planned H team u (Laminate.partner A H) X z-
      WilsonRetainedDecoratedWord.model H p team start u (Laminate.partner A H) X z
    Integrable error (moment X) ∧ (∫z,|error z| ∂moment X)≤
      A.weight*(book u (H.w+carry w) start-book u H.w start)

theorem purchased (R : Run G) (simple : G.Simple) (p j : ℕ) {ε : ℝ} (positive : 0<ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per, m<N →
    let S := R.alloy.B.a.clock.op m per
    let T := ships R.alloy.B N m per
    let s := R.alloy.B.a.clock.hatBeta m
    let g := Pert.Asymptotics.regulatorRun R.family N per (m+1)
    ∀ {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W μ C : ℝ} {o : Target.Order G W}
      {Y : Rep G (R.family.side (m+1) per)} (χ : Chi) (H : Cash W s μ S.patch.L Q o C T Y),
      gStep Y.beta = g →
      (∀ q ≤ S.patch.J, WilsonReportingDecoratedStage.Bought χ H q ∧
        betaF G s S.patch.L ^ (-((q:ℝ)+1-1/2)/2) ≤ (2*g)^((q:ℝ)+1-1/2)) →
      (∀ p ≤ S.patch.J, ∀ j ≤ S.patch.J, ∀ k ≤ S.patch.J, Bought χ H p j k) →
      Word χ H p g ε ∧ Due χ H p j g ε := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt positive
  have small : precision k ≤ ε := by simpa [precision, one_div] using hk.le
  let order := max p (max j k)
  have late := (R.family.path.levels.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop order
  filter_upwards [late,WilsonReportingDecoratedPaidWord.purchased R simple p positive] with
    m height word N per later S T s g P Q W μ C o Y χ H coupling forecast determinant
  have threshold : order ≤ S.patch.J := by
    rw [(Testing.proceeds R.alloy.B N m per later).atStep]
    exact height
  have dl : max j k ≤ order := le_max_right _ _
  obtain ⟨atBond,volume⟩ := determinant p ((le_max_left _ _).trans threshold)
    j ((le_max_left _ _).trans (dl.trans threshold)) k ((le_max_right _ _).trans (dl.trans threshold))
  have charge : precision k*(gStep Y.beta)^p ≤ ε*g^p := by
    rw [← coupling]
    exact mul_le_mul_of_nonneg_right small (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  refine ⟨word N per later χ H forecast,fun i => (atBond i).climb H charge le_rfl,?_⟩
  exact volume.climb H (mul_le_mul_of_nonneg_left charge (Nat.cast_nonneg _)) le_rfl

end YM.Integration.WilsonGaussianDeterminantOrders
