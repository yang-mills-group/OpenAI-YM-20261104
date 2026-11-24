import YM.Integration.WilsonOrdinaryDatedWindows

/-! The actual mixed/two-jet difference is one signed four-term combination of original
positive-measure two-window integrals, with fixed entering charts and one genuine
reflected field per real basis handle. All four measurements use the same physical
cutoff, period and two lattice sites, and their mass is paid before the cutoff. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryWindowBuyer
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable (F : Final R.family f S) (J : ℝ→tower S) (L : Layout F) (g : ℝ→ℝ) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel R.family.book).Field d
local notation "b!" => WilsonOrdinaryHomogeneousDetectors.basis F d
local notation "t!" => (Real.exp (1:ℝ))⁻¹
local notation "E!" => (Real.exp (1:ℝ))

/-- A measured, disjoint, finite original row roster sufficient to price the actual
quadratic comparison. In particular the right label is independent of the four terms. -/
structure WindowRows (A B : Module.End ℂ D) (e : ℕ) (r : ℝ) where
  left : Fin 4 → Handle F d → R.family.label d
  right : Handle F d → R.family.label d
  first z i : master L d r (left z i) = J (radii r t! z) d (columns d t! A B (b! i) z)
  second j : master L d r (right j) = J r d (adjoint R d (b! j))
  first_cost z i : mass R.family d (L.shift d r (left z i)) ≤ R.family.path.levels.clock.hatBeta (L.level r)^e
  second_cost j : mass R.family d (L.shift d r (right j)) ≤ R.family.path.levels.clock.hatBeta (L.level r)^e
  separate p : let k := berth R 28 (L.level r)
    let x := cells R k p r detectors
    let a := omen R.family d k (R.family.path.levels.budget k).B
    Disjoint (window (x 0) a) (window (x 1) a)
  interior (N p : ℕ) : let k := berth R 28 (L.level r)
    k < N → let x := cells R k p r detectors
    let a := omen R.family d k (R.family.path.levels.budget k).B
    (∀ z i, Interior (window (x 0) a) (localized L r d k N p (left z i) (x 0))) ∧
    (∀ j, Interior (window (x 1) a) (localized L r d k N p (right j) (x 1)))
  read : let k := berth R 28 (L.level r)
    ∀ᶠ z : UVIndex in L.lens, k < z.1 ∧ ∀ h i j,
      |mixed F J d r (radii r t! h) (columns d t! A B (b! i) h) (b! j) -
        (WilsonReportWindowMatrix.joint L d ![left h i,right j] r k z.1 z.2).re| ≤ (g r)^2

private lemma term_le {l n : ℕ} (h : Fin l → Fin n → ℝ) (pos : ∀ i j, 0 ≤ h i j)
    (i : Fin l) (j : Fin n) : h i j ≤ ∑ a,∑ b,h a b := by
  exact (single_le_sum (fun b _ => pos i b) (mem_univ j)).trans
    (single_le_sum (fun a _ => sum_nonneg (fun b _ => pos a b)) (mem_univ i))

private lemma dates {r : ℝ} (hr : 0 < r) (i : Fin 4) :
    r/E! ≤ radii r t! i ∧ radii r t! i ≤ E!*r := by
  have hE : 1 ≤ E! := Real.one_le_exp (by norm_num)
  have low : r/E! ≤ r := div_le_self hr.le hE
  have hi : r ≤ E!*r := le_mul_of_one_le_left hr.le hE
  have eq : t!*r = r/E! := by ring
  fin_cases i
  · change r/E! ≤ t!*r ∧ t!*r ≤ E!*r; rw [eq]; exact ⟨le_refl _,low.trans hi⟩
  all_goals exact ⟨low,hi⟩

/-- Issued simultaneously for all horizons and both fixed coefficient maps, preserving
the originally appointed final table, position tower, reader, and real measured stop. -/
theorem on_run (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (fac : OPE.Facilities R.family f S)
    (reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H : Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in trail,Frame.obedient F Y (J r) d) (hg : Coupling G g) :
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex) ≤ f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
      Pier.Scene.ScenePlan R F L ∧ (∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L J) d) ∧
      ∀ (d : ℕ) (A B : Module.End ℂ ((Bel R.family.book).Field d)), ∃ e : ℕ,
        ∀ᶠ r in trail, Nonempty (WindowRows F J L g d A B e r) := by
  obtain ⟨u,Q,L,hu,hQ,atStop,scene,bank,source⟩ := WilsonOrdinaryDatedWindows.on_run hG W original subsidy pace
    hB F fac reader J H paid g hg
  refine ⟨u,Q,L,hu,hQ,atStop,scene,bank,?_⟩
  intro d A B
  let U := Fin 4 × Handle F d
  let a := Fintype.equivFin U
  let b := Fintype.equivFin (Handle F d)
  let X := fun i => columns d t! A B (WilsonOrdinaryHomogeneousDetectors.basis F d (a.symm i).2) (a.symm i).1
  let Y := fun j => WilsonOrdinaryHomogeneousDetectors.basis F d (b.symm j)
  have hE : 1 ≤ E! := Real.one_le_exp (by norm_num)
  obtain ⟨e,read⟩ := source d 2 _ _ X Y hE 1 zero_lt_one
  refine ⟨e,?_⟩
  filter_upwards [read,self_mem_nhdsWithin] with r hr pos
  have gp : 0 < r := pos
  let s := fun i => radii r t! (a.symm i).1
  obtain ⟨v,w,hv,hw,pv,pw,apart,inside,checked⟩ := hr s (fun i => (dates gp _).1) (fun i => (dates gp _).2)
  refine ⟨⟨fun h i => v (a (h,i)),fun j => w (b j),?_,?_,fun h i => pv _,fun j => pw _,apart,?_,?_⟩⟩
  · intro h i; simpa only [X,s,Equiv.symm_apply_apply] using hv (a (h,i))
  · intro j; simpa only [Y,Equiv.symm_apply_apply] using hw (b j)
  · intro N p; dsimp only; intro hk
    exact ⟨fun h i => (inside N p hk).1 (a (h,i)),fun j => (inside N p hk).2 (b j)⟩
  · filter_upwards [checked] with z hz
    refine ⟨hz.1,?_⟩
    intro h i j
    let k := berth R 28 (L.level r)
    let err := fun x y => |mixed F J d r (s x) (X x) (Y y) -
      (WilsonReportWindowMatrix.joint L d ![v x,w y] r k z.1 z.2).re|
    have bound : ∑ x,∑ y,err x y ≤ (g r)^2 := by simpa only [one_mul] using hz.2
    simpa only [err,s,X,Y,Equiv.symm_apply_apply] using
      (term_le err (fun _ _ => abs_nonneg _) (a (h,i)) (b j)).trans bound

/-- The signed genuine two-window cut: four actual integrals sharing the same reflected
representative, cutoff, period and physical measure. -/
def cut {A B : Module.End ℂ D} {e : ℕ} {r : ℝ} (P : WindowRows F J L g d A B e r)
    (z : UVIndex) (i j : Handle F d) : ℝ := signed (g r) (fun h =>
      (WilsonReportWindowMatrix.joint L d ![P.left h i,P.right j] r
        (berth R 28 (L.level r)) z.1 z.2).re)

theorem compared {A B : Module.End ℂ D} {e : ℕ} {r : ℝ} (P : WindowRows F J L g d A B e r)
    (hg : 0 ≤ g r) (cap : g r ≤ 1) : ∀ᶠ z in L.lens, ∀ i j : Handle F d,
    |(mixed F J d r (t!*r) (b! i) (b! j) -
      trialStep F J d r t! (WilsonOrdinaryNormalizedStep.second d (g r) A B) (b! i) (b! j)) -
      cut F J L g d P z i j| ≤ 4*(g r)^2 := by
  filter_upwards [P.read] with z hz
  intro i j
  rw [WilsonOrdinaryFourGram.split]
  exact WilsonOrdinaryFourGram.error hg cap (sq_nonneg _) _ _ (fun h => hz.2 h i j)

/-- A quadratic numerical bound on one registered genuine signed table suffices. The
buyer is expressed entirely on finite Wilson integrals, before the physical limit. -/
theorem measured (hG : G.Simple) (hg : Coupling G g) (A B : Module.End ℂ D) {e : ℕ} {c : ℝ}
    (source : ∀ᶠ r in trail, ∃ P : WindowRows F J L g d A B e r,
      ∀ᶠ z in L.lens,∀ i j, |cut F J L g d P z i j| ≤ c*(g r)^2) :
    MixedError F J d g A B (4+c) := by
  letI := L.notbot
  have small := (Coupling.conforms hG hg).eventually (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))
  filter_upwards [source,hg.positive,small] with r enrolled positive cap
  obtain ⟨P,paid⟩ := enrolled
  obtain ⟨z,close,localPrice⟩ := ((compared F J L g d P positive.le cap.le).and paid).exists
  intro i j
  let v := mixed F J d r (t!*r) (b! i) (b! j) -
    trialStep F J d r t! (WilsonOrdinaryNormalizedStep.second d (g r) A B) (b! i) (b! j)
  let w := cut F J L g d P z i j
  calc
    |v| = |(v-w)+w| := by rw [sub_add_cancel]
    _ ≤ |v-w|+|w| := abs_add_le _ _
    _ ≤ 4*(g r)^2+c*(g r)^2 := add_le_add (close i j) (localPrice i j)
    _ = _ := by ring

end YM.Integration.WilsonOrdinaryWindowBuyer
