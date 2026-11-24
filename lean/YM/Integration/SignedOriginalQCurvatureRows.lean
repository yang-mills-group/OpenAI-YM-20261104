import YM.Integration.FundedOriginalMarkedInput
import YM.Integration.ActualOriginalQFrozenInput

/-! Literal charged opening vertices in the genuine fixed-Q source, before field derivatives
or the Gaussian integration. Each chosen field and its independent test retain their phases. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedOriginalQCurvatureRows
open Function Finset Lattice Wilson RG Source Labels Marker Extra.Histories
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Mosaic.Near
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address RG05Readout.Native
open Comparison.Density.RenderM ActualRunCalibrationTests NativeCurvatureTensor
open ActualRunKernelPackets ActualRunCurvaturePackets ActualOriginalQReaders
open OriginalSourceJetAddresses OriginalMarkedSourceComet IndependentSourcePathFamily
open FundedOriginalMarkedInput
open scoped Classical BigOperators Topology

private theorem val_of_heq {n m : ℕ} {a : Fin n} {b : Fin m} (h:n=m) (e:HEq a b) : a.val=b.val := by
  subst m;exact congrArg Fin.val (eq_of_heq e)

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G} {period L n : ℕ} {hn : n ≤ L}
variable {V : Type} [Fintype V] [DecidableEq V]
variable (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R period L n hn V)
variable (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (scale : V → ℂ)
local notation "O" => ActualRunQlocalNativeTuple.orbit D
local notation "dim₀" => FundedOriginalMarkedInput.OrbitD D
local notation "n₀" => R.family.side L period
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u

def tests (x : TestSpace (O)) (choice : V → Bool) : Case (dim₀) :=
  fun v => page _ (project ((O) v) (x v) (component (choice v)))

def currentAt (i : V) (b : Count D u i) (choice : V → Bool) :
    Comet G (Pen (dim₀) {i}) ((chosen Q D u μ orders scale choice i b).rank) :=
  let a := chosen Q D u μ orders scale choice i b
  current (colour a.path a.color a.weight a.quadrant) (petal (dim₀) i (claim _ a.knob a.point))

private theorem pair (z t : ℂ) :
    z*t = ∑ b : Bool × Bool, (phase b.1*phase b.2)*
        ((component b.2 t * component b.1 z : ℝ):ℂ) := by
  calc
    _ = (∑ h : Bool, phase h * (component h z:ℂ)) *
        (∑ h : Bool, phase h * (component h t:ℂ)) := by rw [resolve,resolve]
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      apply sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro j _
      push_cast
      ring

def physical (s : Rows) (U : Config G (n₀)) : ℂ :=
  let a := (ofRun R ((ActualOriginalQPackets.degree u) s.1)).data
  NativeCurvatureTensor.value (fun h => (word s.2.2.val h).2)
    (fun h => (a.columns s.2.1 (word s.2.2.val h).1).atSite U (ActualRunQlocalNativeTuple.root D s.1.1))

def numerical (s : Rows) : ℂ :=
  MvPolynomial.coeff s.2.2.val ((ofRun R ((ActualOriginalQPackets.degree u) s.1)).data.shape s.2.1) *
    ActualOriginalQReaders.coordinates (R:=R) u s.1 s.2.1

def address (s : Rows) (a : Word (depth (D.choice s.1.1).2.1)) : ℂ :=
  ActualOriginalQReaders.fee Q u μ orders s.1 * Motion.scalar (D.motion s.1.1)
    (ActualRunQlocalNativeTuple.constant D s.1.1 * multiplier (D.choice s.1.1).2.1
      ((R.family.S.toDepth hn period).count.val:ℝ)⁻¹ a)

def derivative (i : V) (a : Word (depth (D.choice i).2.1)) (x : TestSpace (O)) : ℂ :=
  OriginalSourceJetAddresses.jet (depth (D.choice i).2.1) a
    (place (R.family.S.toDepth hn period) (D.choice i).1).val (x i).val

omit [Fintype V] [DecidableEq V] in
/-- The coupling factors are canceled on the original finite primitive, retaining its
entire holonomy field, the chosen source normalizer and every original derivative word. -/
theorem row (N : ℕ) (hN : L ≤ N) (s : Rows) (x : TestSpace (O)) (U : Config G (n₀)) :
    scale s.1.1 *
      (Pert.Asymptotics.regulatorRun R.family N period L : ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s:ℤ)) *
        (ActualOriginalQPackets.token Q D u μ orders N s).read x U =
      ∑ a : Word (depth (D.choice s.1.1).2.1),
        (scale s.1.1 * numerical u s * address Q D u μ orders s a * physical D u s U) *
          derivative D s.1.1 a x := by
  let T := ActualOriginalQPackets.token Q D u μ orders N s
  let H := fun j : Fin (tokenRank R (ActualOriginalQPackets.degree u) s) → G.ColorIndex =>
    ((∏ h, (T.path h).atSite U T.root (j h):ℝ):ℂ)
  let Z := (Pert.Asymptotics.regulatorRun R.family N period L:ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s:ℤ))
  have hgem (j) : Z*T.gem j x =
      ∑ a, ((NativeCurvatureTensor.coefficient (fun h => (word s.2.2.val h).2) j * numerical u s) *
        address Q D u μ orders s a) * derivative D s.1.1 a x :=
    OriginalSourceJetAddresses.addressed Q D u μ orders N hN s j x
  have hcurv : physical D u s U = ∑ j, H j * NativeCurvatureTensor.coefficient
      (fun h => (word s.2.2.val h).2) j := rfl
  change scale s.1.1 * Z * (∑ j, H j * T.gem j x) = _
  rw [Finset.mul_sum]
  calc
    _ = ∑ j, ∑ a, (scale s.1.1 * numerical u s * address Q D u μ orders s a *
          (H j * NativeCurvatureTensor.coefficient (fun h => (word s.2.2.val h).2) j)) *
          derivative D s.1.1 a x := by
      apply sum_congr rfl
      intro j _
      rw [show scale s.1.1*Z*(H j*T.gem j x) = scale s.1.1*H j*(Z*T.gem j x) by ring,
        hgem,Finset.mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ = _ := by
      rw [sum_comm,hcurv]
      apply sum_congr rfl
      intro a _
      rw [Finset.mul_sum,Finset.sum_mul]

omit [Fintype V] in
/-- Equality of the independently defined original bounded current and the entire
quadrature of its measured finite curvature, including the original nonzero source value. -/
theorem sectionRead (i : V) (s : {s : Rows // s.1.1 = i}) (a : Word (depth (D.choice i).2.1))
    (x : TestSpace (O)) (U : Config G (n₀)) (h t : V → Bool) :
    (dip (currentAt Q D u μ orders scale i (s,a) h) (touch (tests D x t) {i})).unmasked U
      (ActualRunQlocalNativeTuple.root D i) =
        component (t i) (derivative D i a x) *
          component (h i) ((chosen Q D u μ orders scale h i (s,a)).weight * physical D u s.val U) := by
  rcases s with ⟨s,rfl⟩
  let b := chosen Q D u μ orders scale h s.1.1 (⟨s,rfl⟩,a)
  let o := (R.family.S.toDepth hn period)
  let f := fun v => project ((O) v) (x v) (component (t v))
  have hpair := OriginalMarkedSourceComet.paired (dim₀) s.1.1 b.path b.color b.weight b.quadrant
    (D.depth_le s.1.1) a (place o (D.choice s.1.1).1) f U (ActualRunQlocalNativeTuple.root D s.1.1)
  have hjet := OriginalMarkedSourceComet.project_jet ((O) s.1.1) (x s.1.1)
    (component (t s.1.1)) (D.depth_le s.1.1) a (place o (D.choice s.1.1).1)
  rw [show SignedOriginalQCurvatureRows.tests D x t = (fun v => page ((dim₀) v) (project ((O) v) (x v) (component (t v)))) from rfl]
  simp only [currentAt,b,f,o,hjet,derivative,chosen,physical] at hpair ⊢
  convert hpair using 1
  congr! <;> first | rfl | exact val_of_heq (by assumption) (by assumption) | exact eq_of_heq (by assumption)

omit [Fintype V] in
/-- Both complex phases are put back after the physical measurements using the actual
normalized charged row at this finite cutoff. Each phase choice may be independent across marks. -/
theorem measured (N : ℕ) (hN : L ≤ N) (i : V) (s : {s : Rows // s.1.1=i})
    (x : TestSpace (O)) (U : Config G (n₀)) :
    scale i *
      (Pert.Asymptotics.regulatorRun R.family N period L:ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s.val:ℤ)) *
        (ActualOriginalQPackets.token Q D u μ orders N s.val).read x U =
      ∑ a : Word (depth (D.choice i).2.1), ∑ b : Bool × Bool,
        (phase b.1 * phase b.2) *
          ((dip (currentAt Q D u μ orders scale i (s,a) (fun _ => b.1))
            (touch (tests D x (fun _ => b.2)) {i})).unmasked U (ActualRunQlocalNativeTuple.root D i):ℂ) := by
  rcases s with ⟨s,rfl⟩
  rw [row Q D u μ orders scale N hN s x U]
  apply sum_congr rfl
  intro a _
  rw [pair]
  apply sum_congr rfl
  intro b _
  rw [sectionRead]
  simp only [chosen,numerical,address]

omit [Fintype V] [DecidableEq V] in
private theorem scaled {N : ℕ} (hN : L ≤ N) (s : Rows) (x : TestSpace (O)) (U : Config G (n₀)) :
    (Pert.Asymptotics.regulatorRun R.family N period L:ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s:ℤ)) *
        (ActualOriginalQPackets.token Q D u μ orders N s).read (fun i => scale i • x i) U =
      scale s.1.1 *
        (Pert.Asymptotics.regulatorRun R.family N period L:ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s:ℤ)) *
          (ActualOriginalQPackets.token Q D u μ orders N s).read x U := by
  let T := ActualOriginalQPackets.token Q D u μ orders N s
  let Z := (Pert.Asymptotics.regulatorRun R.family N period L:ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) s:ℤ))
  let h (j : Fin (tokenRank R (ActualOriginalQPackets.degree u) s) → G.ColorIndex) :=
    ((∏ a,(T.path a).atSite U T.root (j a):ℝ):ℂ)
  have value (j) : Z*T.gem j (fun i => scale i • x i) = scale s.1.1*(Z*T.gem j x) := by
    rw [OriginalSourceJetAddresses.primitive Q D u μ orders N hN s j,
      OriginalSourceJetAddresses.primitive Q D u μ orders N hN s j,map_smul,smul_eq_mul]
    ring
  change Z * ∑ j, h j*T.gem j (fun i => scale i • x i) =
    scale s.1.1*Z * ∑ j, h j*T.gem j x
  rw [Finset.mul_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  calc _ = h j*(Z*T.gem j (fun i => scale i • x i)) := by ring
       _ = _ := by rw [value]; ring

theorem frozen (N : ℕ) (x : TestSpace (O)) (g : ℝ) (s : (Stock.census V).Mode) (U : Config G (n₀)) :
    ((ActualOriginalQFrozenInput.packets Q D u μ orders N).read x g U).part s =
      ∑ a : Rows, if s = (Stock.census V).fire a.1.1 then
        (Pert.Asymptotics.regulatorRun R.family N period L:ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) a:ℤ)) *
          (ActualOriginalQPackets.token Q D u μ orders N a).read x U else 0 := by
  unfold ActualOriginalQFrozenInput.packets
  rw [ActualPacketCouplingFreeze.freeze_read]
  unfold ActualOriginalQPackets.packets
  rw [MarkedPackets.ofFin_read,Poly.part_sum]
  simp only [Poly.part_send]
  apply Fintype.sum_equiv (Fintype.equivFin (Rows)).symm
  intro i
  rfl

def field (s : Rows) (x : TestSpace (O)) (U : Config G (n₀)) : ℂ :=
  ∑ a : Word (depth (D.choice s.1.1).2.1), ∑ b : Bool × Bool,
    (phase b.1*phase b.2) *
      ((dip (currentAt Q D u μ orders scale s.1.1 (⟨s,rfl⟩,a) (fun _ => b.1))
        (touch (tests D x (fun _ => b.2)) {s.1.1})).unmasked U (ActualRunQlocalNativeTuple.root D s.1.1):ℂ)

/-- Actual complete normalized startup packet on every original field. In the raw input
only singleton marks are present; all compound moments arise from its genuine exponential. -/
theorem complete (N : ℕ) (hN : L ≤ N) (x : TestSpace (O)) (g : ℝ)
    (s : (Stock.census V).Mode) (U : Config G (n₀)) :
    ((ActualOriginalQFrozenInput.packets Q D u μ orders N).read (fun i => scale i • x i) g U).part s =
      ∑ a : Rows, if s=(Stock.census V).fire a.1.1 then field Q D u μ orders scale a x U else 0 := by
  rw [frozen]
  apply sum_congr rfl
  intro a _
  by_cases h : s=(Stock.census V).fire a.1.1
  · simp only [h,if_true]
    exact (scaled Q D u μ orders scale hN a x U).trans
      (measured Q D u μ orders scale N hN a.1.1 ⟨a,rfl⟩ x U)
  · simp only [h,if_false]

end YM.Integration.SignedOriginalQCurvatureRows
end
