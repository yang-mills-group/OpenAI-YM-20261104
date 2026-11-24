import YM.Integration.WilsonCubicOriginalTorus
import YM.Integration.WilsonVacuumPreResetJointSeating
import YM.Integration.WilsonVacuumPreResetJointStack

/-! The authenticated winding book of a single issued row at every rank.
The lag uses that exact row's nominal grade and rank, including rank zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointPublished
open WilsonCoeffUV
open Filter Function Finset Matrix Lattice Wilson RG Laurent Bloch Exterior Blue FreeResolvent Work.F08 Precision
open Gauge WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Power Near Stationary PowerSeries
open Work.G05 Tree Pressure Pressure.Stores Pressure.Tube ConnectedActivityE6 SliceRows Coat Matter
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {σ C : ℝ}

def lag (a : PrismA G) (k : ℕ) : ℕ := a.grade+(k-(a.rise+2))

theorem rank (a : PrismA G) (hs : 0 < σ) (bank : Commission a.cells σ C a.grade) (k : ℕ) :
    surf a f (lag a k) k = rye (turnSeries a.cells (m:=f)) k := by
  have ge : a.grade ≤ lag a k := Nat.le_add_right _ _
  have step : lag a k - a.grade = k-(a.rise+2) := by simp [lag]
  simp only [Mosaic.surf,ge,if_pos,sprig]
  rw [step]
  by_cases small : k<a.rise+2
  · have smooth : Green (turnSeries a.cells (m:=f)) := (turns_analytic a.cells hs bank.toll).contDiffAt
    have vanish := (rays_jet smooth.analyticAt (a.rise+2)).1 (turns_low a.cells hs bank.toll) k small
    rw [Blue.shine_dark (by omega : a.rise+2+(k-(a.rise+2)) ≠ k)]
    funext x
    simp [rye,vanish]
  · have same (l : ℕ) (h : l=k) :
        Blue.shine (rye (turnSeries a.cells (m:=f)) l) k = rye (turnSeries a.cells (m:=f)) k := by
      subst l
      exact Blue.shine_lit _
    exact same _ (by omega)

theorem winding (a : PrismA G) (hs : 0 < σ) (bank : Commission a.cells σ C a.grade) (k : ℕ) :
    rye (turnSeries a.cells (m:=f)) (k+1) =
      lagoon (huesT (recordV a (lag a (k+1)) (k+1))) f := by
  rw [← rank a hs bank (k+1)]
  exact stands_self hs a bank (lag a (k+1)) k f

def polynomial (a : PrismA G) (d : ℕ) (v : Link G f) : ℝ :=
  ∑ k ∈ range (d+1), MvPolynomial.eval v (paint k (surf a f (lag a k) k))

theorem printed (a : PrismA G) (hs : 0 < σ) (bank : Commission a.cells σ C a.grade) (d : ℕ) :
    polynomial a d = blockTaylor d (turnSeries a.cells (m:=f)) := by
  funext x
  unfold polynomial blockTaylor
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [rank a hs bank,← jet_apply]
  exact rayon _ _ _

def realRead (a : PrismA G) (U : Config G f) : ℝ :=
  Patch.average fun s : Signed => Precision.uncut a.cells (pull s 0 U)

private theorem raw (a : PrismA G) (v : Directions G f) :
    realRead a (RG.increment 1 v) = turnSeries a.cells (WilsonCubicOriginalTorus.coordinates G f v) := by
  change realRead a (RG.increment 1 v) =
    realRead a (represent (arm G f 1 ((arm G f 1).symm (toLog v))))
  rw [ContinuousLinearEquiv.apply_symm_apply, edits]

theorem seated (a : PrismA G) (hs : 0 < σ) (bank : Commission a.cells σ C a.grade)
    (X : Coat T F) (p : Molecule S) (kept : p.toLeft=∅)
    (sun : flags (Pressure.temp X.x) X.V=∅) (Y : F.Slice G) (d : ℕ) :
    let Z := (Matter.planted X p).wrapY Y
    let u := WilsonCubicOriginalTorus.coordinates G f ∘ changes univ Z
    ∀ k≤d, iteratedFDeriv ℝ k (realRead a ∘ field univ Z) 0 =
      iteratedFDeriv ℝ k (polynomial a d ∘ blockTaylor d u) 0 := by
  let Z := (Matter.planted X p).wrapY Y
  let U := field univ Z
  let u := WilsonCubicOriginalTorus.coordinates G f ∘ changes univ Z
  let v := turnSeries a.cells (m:=f)
  have at0 : U 0=1 := WilsonVacuumPreResetJointBranch.base X p kept sun Y
  have agree : realRead a ∘ U =ᶠ[𝓝 0] v ∘ u := by
    filter_upwards [agrees univ Z] with z hz
    change realRead a (U z) = turnSeries a.cells (WilsonCubicOriginalTorus.coordinates G f (changes univ Z z))
    rw [show U z=RG.increment (U 0) (changes univ Z z) from hz,at0,raw]
  have zero : u 0=0 := by simp [u,changes_zero]
  have ht : ContDiffAt ℝ d u 0 := (WilsonCubicOriginalTorus.coordinates G f).contDiff.contDiffAt.comp _
    ((smooth univ Z).of_le le_top)
  have hv : ContDiffAt ℝ d v 0 := (turns_analytic a.cells hs bank.toll).contDiffAt.of_le le_top
  have z0 : blockTaylor d u 0=0 := (blockTaylor_zero d u).trans zero
  have eq := jets_comp (x:=0) (g:=v) (g':=blockTaylor d v) ht (blockTaylor_contDiff d u _).contDiffAt
    (zero.symm ▸ hv) (blockTaylor_contDiff d v _).contDiffAt (zero.trans z0.symm)
    (fun k hk => (blockTaylor_jets ht k hk).symm)
    (fun k hk => by rw [z0]; exact (blockTaylor_jets hv k hk).symm)
  dsimp only
  intro k hk
  rw [printed a hs bank]
  exact ((agree.iteratedFDeriv ℝ k).eq_of_nhds).trans (eq k hk)

end YM.Integration.WilsonVacuumPreResetJointPublished
