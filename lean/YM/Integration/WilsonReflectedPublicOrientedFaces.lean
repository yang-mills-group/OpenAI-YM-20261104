import YM.Integration.WilsonAddressedPublicOriginalFaces
import YM.Integration.WilsonReflectedPublicAlignedPoints
/-! The complete true normalized cutoff density of a submitted, rooted and
individually reflected finite portfolio on the same reported grid. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicOrientedFaces
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {N p k : ℕ} {I : Type} [Fintype I] [DecidableEq I]
local notation "C₀" => R.family

def displayed (d : ℕ) (x : (C₀).label d) (t : Motion) : (C₀).label d :=
  ((C₀).labels.level d).act t.1.ortho (if t.2 then star x else x)

omit [Fintype I] [DecidableEq I] in
theorem arm (d : I → ℕ) (x : (i : I) → (C₀).label (d i))
    (V : (i : I) → Sight C₀ (d i) p) (u : (i : I) → Emblems C₀ (d i))
    (est : ∀i, Opened C₀ (d i) k p) (hk : k ≤ N)
    (raw : ∀ i, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (d i)
      (digits R N p 0) (V i) (u i)) (ref : ∀i e, e ≤ d i → (C₀).ref e ≤ N)
    (turn : I → Motion) (c : I → Site ((C₀).side k p)) (i : I) :
    let y := fun a => offer R (x a) (est a) hk
    let b := WilsonThermometerReflectedTrajectory.anchorAt R (c i) N
    WilsonThermometerReflectedRoster.source R d (fun _ => 0) turn c
      (fun a => reduce (y a)) u hk i =
      ((charge (y i):ℝ):ℂ)⁻¹ • (C₀).O N p (displayed R (d i) (x i) (turn i)) b := by
  intro y b
  let α : ℂ := ((C₀).S.a k:ℂ)^(d i)
  let χ : ℂ := ((charge (y i):ℝ):ℂ)⁻¹
  let T := (C₀).factory (d i) N p
  let w := T.terminal (finer (u i) hk (y i) (primaryLetter (d i)))
  have point : α • w = x i := (WilsonAddressedAlignedColumn.original R (raw i) hk le_rfl
    (ref i) (est i) (x i)).1
  have head : T.terminal (finer (u i) hk (reduce (y i)) (primaryLetter (d i))) = χ • w := by
    rw [reduce,map_smul,Pi.smul_apply];exact T.terminal.map_smul _ _
  have birth : WilsonThermometerIntrinsicRoster.source R d (fun _ => 0) (fun a => reduce (y a)) u hk i =
      χ • (C₀).O N p (x i) 0 := by
    unfold WilsonThermometerIntrinsicRoster.source WilsonThermometerOwnOffsetNectar.birth
    rw [head,←point,((C₀).linearO N p (d i) 0).map_smul,((C₀).linearO N p (d i) 0).map_smul,smul_comm]
  rw [WilsonThermometerReflectedRoster.source,birth]
  funext W
  let t := turn i
  have placed (v : (C₀).label (d i)) :
      (C₀).O N p (((C₀).labels.level (d i)).act t.1.ortho v) b W =
      (C₀).O N p v 0 (pull t.1 b W) := by
    simpa [affine] using
      (C₀).rotated R.makes (ref i (d i) le_rfl) v t.1 0 b W
  change scalar t (χ * (C₀).O N p (x i) 0 (pull t.1 b W)) =
    χ * (C₀).O N p (displayed R (d i) (x i) t) b W
  rw [displayed,placed,scalar_mul]
  have real : scalar t χ = χ := by
    dsimp only [scalar,χ]
    split <;> simp
  rw [real]
  dsimp only [scalar]
  split
  · rw [(C₀).reality R.makes (ref i (d i) le_rfl)]
  · rfl

theorem original (d : I → ℕ) (x : (i : I) → (C₀).label (d i))
    (V : (i : I) → Sight C₀ (d i) p) (u : (i : I) → Emblems C₀ (d i))
    (est : ∀i, Opened C₀ (d i) k p) (hk : k ≤ N)
    (raw : ∀i, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (d i)
      (digits R N p 0) (V i) (u i)) (ref : ∀i e, e ≤ d i → (C₀).ref e ≤ N)
    (turn : I → Motion) (c : I → Site ((C₀).side k p)) (names : Census I) (t : ℕ) :
    let y := fun i => offer R (x i) (est i) hk
    let b := fun i => WilsonThermometerReflectedTrajectory.anchorAt R (c i) N
    let data := fun i => reduce (y i)
    WilsonThermometerReflectedRoster.filed R d (fun _ => 0) turn c data V u names hk t →
    ∀ j (hj : j ≤ N) (s : names.Mode) U,
      (WilsonThermometerReflectedRoster.density R d (fun _ => 0) turn c data u names hk hj U).part s =
      ((C₀).path.rep N p j).eval U • actualTransport C₀ (N:=N)
        (fun W => ∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (displayed R (d i) (x i) (turn i)) (b i) W) hj U := by
  intro y b data filed j hj s U
  let f := WilsonThermometerReflectedRoster.source R d (fun _ => 0) turn c data u hk
  let bank := (C₀).path.rep N p
  have bill := (filed N hk (le_refl _)).1
  simp only [WilsonThermometerReflectedRoster.density,gust_base] at bill
  rw [WilsonThermometerReflectedRoster.density,actualTransport_unnormalize C₀ R.makes (le_refl N)]
  have face := congr_fun (pushpart hj (Accent.birth names (bank N) f) s bill) U
  rw [face]
  have exactField (W) : ((Accent.birth names (bank N) f) W).part s = (bank N).eval W •
      (∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (displayed R (d i) (x i) (turn i)) (b i) W) := by
    unfold Accent.birth Accent.Mach
    rw [Poly.part_smul,pass_fire,Complex.real_smul]
    congr 1
    exact prod_congr rfl fun i _ => congrFun (arm R d x V u est hk raw ref turn c i) W
  simp_rw [exactField];rfl

end YM.Integration.WilsonReflectedPublicOrientedFaces
end
