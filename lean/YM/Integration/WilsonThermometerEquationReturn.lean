import YM.Integration.WilsonThermometerEquationDisplacements
import YM.Integration.WilsonThermometerSelectedDisplacements
import YM.FullVolume.Ocean

/-! The original signed canonical-match error at arbitrary displaced cells.
The charge is linear in the actual bare equation coordinates, even when their
size, direction, cutoff and displacement all vary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerEquationReturn
open Function Filter Set MeasureTheory Lattice RG Labels Wilson Source Bid Cells
open PhysicalNext.Repeat.Legato WilsonLimitConstruction MergeProof Push FullVolume
open Extraction Extraction.Lease Next.Extract Org RelayDifference
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)
local notation "C" => R.family

private def read {d : ℕ} (V : SectionData (R.family.labels.level d)) (N p : ℕ)
    (o : Site (R.family.side N p)) : R.family.label d →ₗ[ℂ] (Config G (R.family.side N p) → ℂ) where
  toFun v := initial V R.family.path N p v o
  map_add' x y := by
    funext u
    simp [initial,SectionData.places,V.eval_linear.map_add,mul_add]
  map_smul' q v := by
    funext u
    simp only [initial,map_smul,SectionData.places,V.eval_linear.map_smul,Pi.smul_apply]
    exact smul_comm _ _ _

/-- The difference of the actual calibrated Wilson cylinder and the exact
alternate equation stencil on the same family. -/
def difference {d : ℕ} (V : SectionData (R.family.labels.level d))
    (U : ℕ → ℕ → R.family.label d ≃ₗ[ℂ] R.family.label d) (N p : ℕ)
    (o : Site (R.family.side N p)) : R.family.label d →ₗ[ℂ] (Config G (R.family.side N p) → ℂ) :=
  (((R.family.linearO N p d o).mk' _).comp
    (((R.family.factory d N p).terminal).toLinearMap.comp (U N p).toLinearMap)) - read R V N p o

theorem returned (simple : G.Simple) {V : ∀ d,SectionData (R.family.labels.level d)} {W : Mark.Weave G} {U e}
    (issued : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (witness : Hearthside C V W U e (Bandage.fly R.alloy.B.a)) (d : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∃ h : k≤N, ∀ p (v : R.family.label d)
      {m : ℕ} (earlier : m≤k) (t : Site (R.family.side m p)) (o : Site (R.family.side N p)),
      let T := center R.family.S p (earlier.trans h) 0
      o ∈ T.margin t (3*span R.family.S h p) →
      ∃ H : Config G (R.family.side N p) → ℂ, Interior (T.chamber 0) H ∧
        T.rootTest (R.family.beta N p) H ≤ (R.family.labels.level d).coeffSize v *
          Real.exp (-(1/32:ℝ)*R.family.S.scale N) ∧
        T.copy t H = difference R (V d) (fun n q=>U d (n,q)) N p o v := by
  obtain ⟨E,Y,hY⟩ := witness.hearth d
  let I := (R.family.labels.level d).Index
  let basis (i:I) : R.family.label d := Pi.single i 1
  have rows (i:I) := (ocean R.makes (R.again simple).1.tabs (V d) (issued d).valid hY
    (fun _ => basis i) (Sluggish.const (basis i))).2
  filter_upwards [eventually_all.mpr rows] with k data
  filter_upwards [eventually_all.mpr (fun i => FullVolume.late.mp (data i)),
    eventually_ge_atTop k] with N stock h
  refine ⟨h,?_⟩
  intro p v m earlier t o T inside
  let L := difference R (V d) (fun n q=>U d (n,q)) N p 0
  let S := center R.family.S p h 0
  have tags (i:I) : Interior (S.chamber 0) (L (basis i)) ∧
      S.rootTest (R.family.beta N p) (L (basis i)) ≤ Real.exp (-(1/32:ℝ)*R.family.S.scale N) :=
    (stock i p).choose_spec
  have sum : ∑ i : I, v i • basis i = v := by
    funext j
    rw [Finset.sum_apply,Finset.sum_eq_single j]
    · simp [basis]
    · intro i _ ij
      simp [basis,Ne.symm ij]
    · simp
  have priced := Next.UVStress.root_sum S (R.family.beta N p) Finset.univ (fun i=>L (basis i))
    v (fun i _=>(tags i).1) (seamless R.makes N p)
  have assembled : ∑ i,v i • L (basis i) = L v := by
    rw [←sum, map_sum]
    simp only [map_smul]
    rw [sum]
  rw [assembled] at priced
  have rate : S.rootTest (R.family.beta N p) (L v) ≤ (R.family.labels.level d).coeffSize v *
      Real.exp (-(1/32:ℝ)*R.family.S.scale N) := by
    rw [Frame.coeffSize,Finset.sum_mul]
    exact priced.2.trans (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (tags i).2 (norm_nonneg _)))
  obtain ⟨H,good,bill,eq⟩ := Frontier6.Platform.moved_basis R.makes h earlier t priced.1 rate inside
  refine ⟨H,good,bill,eq.trans ?_⟩
  funext xs
  change R.family.O N p _ 0 (Lattice.translate o xs) - initial (V d) R.family.path N p v 0 (Lattice.translate o xs) =
    R.family.O N p _ o xs - initial (V d) R.family.path N p v o xs
  rw [R.family.translation,zero_add]
  unfold initial
  simp

end YM.Integration.WilsonThermometerEquationReturn
