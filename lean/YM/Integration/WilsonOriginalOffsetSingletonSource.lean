import YM.Integration.WilsonThermometerOffsetPhysical
import YM.Integration.LocalComparisonInterface

/-! The full paid elementary rows and the signed tail at an arbitrary original
child history, in the coordinates of a fixed reporting date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOffsetSingletonSource
open Function Set Filter MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest MergeProof Accent PhysicalNext.Repeat.Legato
open WilsonThermometerOffsetTrajectory
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {d m i N p : ℕ}
private theorem aligned {C : Family G} (r : Emblems C d) (u : Palette C d)
    (later : m ≤ i) (reached : i ≤ N) :
    finer r later (Many.point r u N m) = Many.point r u N i := by
  unfold Many.point
  simp only [dif_neg (not_lt.mpr (later.trans reached)),dif_neg (not_lt.mpr reached)]
  rw [Many.sumwalk r later reached]
  exact LinearEquiv.apply_symm_apply _ _

structure Inventory (d N p i : ℕ) (coordinate : Palette R.family d) (source : Tape G (R.family.side i p))
    (signed : Body → Goods G (R.family.side i p)) (cap : ℝ) where
  rows : lows R.family (R.family.side i p) d
  tail : Tape G (R.family.side i p)
  wages : Letter d → ℝ
  rest : ℝ
  issued : Necklace (R.family.labels.level 0) (R.family.localSection 0) R.family.params
    (R.family.path.rep N p i) 0 (LocalComparison.forcedDivisor R.family i) d tail rest
  located (l : Letter d) : (rows l).Format 0 R.family.params (R.family.path.rep N p i)
  paid (l : Letter d) : (rows l).remBound 0 (R.family.path.rep N p i)
    (LocalComparison.forcedDivisor R.family i) (wages l)
  total : (∑ l,wages l)+rest ≤ cap
  each (l : Letter d) : wages l ≤ cap
  germ (l : Letter d) : Trace.Physical.Germ.projection (R.family.labels.level (kept l))
    R.family.params (R.family.path.rep N p i).p.threshold 0 (rows l) = coordinate l
  table : together R.family (R.family.path.rep N p i) 0 d rows + tail = source
  measured : pulseOut source = signed

theorem original (simple : G.Simple) (purchase : RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ B : ℕ → ℕ → ℝ, ∀ d (ε : ℝ), 0<ε → ∀ᶠ m : ℕ in atTop,
      ∀ p N, m≤N → ∀ sites : ∀ j, Bud R.family p j,
      ∃ V r, Enrolled R.makes R.doors B m N p d sites V r ∧
        ∀ (i : ℕ) (_later : m ≤ i) (reached : i ≤ N) (_starts : ∀ e ≤ d, R.family.ref e ≤ N),
        ∀ (t : Letter d) (x : R.family.label (kept t)),
          let raw := chunk t ((R.family.factory (kept t) N p).terminal.symm x)
          Nonempty (Inventory R d N p i (Many.point r raw N i) (V i (Many.point r raw N i))
            (fun φ => dyes R.family i N p reached
              (WilsonThermometerOffsetPhysical.route R N p i d sites (N-i) (by omega)
                (WilsonReportingUVReturn.raw R N p t x) φ))
            (B d i*(Real.exp (ε*(R.family.S.scale i-R.family.S.scale m))*
              size (Many.point r raw N m)))) := by
  obtain ⟨B,bought⟩ := WilsonThermometerOffsetTrajectory.original R simple purchase
  refine ⟨B,fun d ε positive => ?_⟩
  filter_upwards [bought d ε positive] with m take p N top sites
  obtain ⟨V,r,H,mass⟩ := take p N top sites
  refine ⟨V,r,H,fun i later reached starts t x => ?_⟩
  let u := chunk t ((R.family.factory (kept t) N p).terminal.symm x)
  let cap := B d i*(Real.exp (ε*(R.family.S.scale i-R.family.S.scale m))*size (Many.point r u N m))
  have G₀ := H.legal i later reached
  have scale := mass i later reached (Many.point r u N m)
  have align := aligned (C:=R.family) (d:=d) r u later reached
  have sized := congrArg (size (C:=R.family)) align
  have scale₀ := le_trans sized.symm.le scale
  obtain ⟨_,L⟩ := G₀.capacity0 (Many.point r u N i)
  rcases L with @⟨rows,tail,wages,rest,issued,placed,price,table,_,jets,sum⟩
  have funded : (∑ l,wages l)+rest ≤ cap :=
    sum.trans (mul_le_mul_of_nonneg_left scale₀ (zero_le_one.trans G₀.pos))
  exact ⟨⟨rows,tail,wages,rest,issued,placed,price,funded,fun l =>
    (Finset.single_le_sum (f:=wages) (fun j _ => rem_nonneg (price j)) (Finset.mem_univ l)).trans
      ((le_add_of_nonneg_right issued.nonneg).trans funded),fun l => (congrFun jets l).symm,table,
    WilsonThermometerOffsetPhysical.original R N p H later reached starts t x⟩⟩

end YM.Integration.WilsonOriginalOffsetSingletonSource
end
