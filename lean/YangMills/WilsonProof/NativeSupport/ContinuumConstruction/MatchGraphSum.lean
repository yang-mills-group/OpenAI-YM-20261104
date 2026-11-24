import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.StandaloneCorrelation
import YM.MS.Graphical.CommonGates
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option quotPrecheck false

namespace ContinuumConstruction.MatchAllocation.PostedFieldDegreeAllocations
open YM.XSpace.Normalize Finset
open scoped Classical BigOperators
noncomputable section
variable {n k : ℕ}

private theorem total (a : Days n) : a ∈ tally k n ↔ a none + ∑ i, a (some i) = k := by
  simp [tally, Finset.mem_finsuppAntidiag, Fintype.sum_option]

private def degree (a : Days n) (ha : a ∈ tally k n) (i : Fin n) : Fin (k+1) :=
  ⟨a (some i), by
    have hsum := (total a).mp ha
    have hi := Finset.single_le_sum (f:=fun i => a (some i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega⟩

theorem original (G : ℕ → (Fin n → ℕ) → ℂ) :
    ∑ a ∈ tally k n, G (a none) (fun i => a (some i)) =
    ∑ v : Fin n → Fin (k+1), if (∑ i, (v i).val) ≤ k then G (k-∑ i, (v i).val) (fun i => (v i).val) else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a ha => degree a ha)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := (total a).mp ha
    change (∑ i, a (some i)) ≤ k
    omega
  · intro a ha b hb eq
    have hs (i : Fin n) : a (some i) = b (some i) := congrArg Fin.val (congrFun eq i)
    have hass := (total a).mp ha
    have hbss := (total b).mp hb
    ext i
    cases i with
    | none => simp_rw [hs] at hass; omega
    | some i => exact hs i
  · intro v hv
    have bound := (Finset.mem_filter.mp hv).2
    let f : Option (Fin n) → ℕ := Option.elim' (k - ∑ i, (v i).val) (fun i => (v i).val)
    let a : Days n := Finsupp.equivFunOnFinite.symm f
    have ha : a ∈ tally k n := by
      apply (total a).2
      exact Nat.sub_add_cancel bound
    refine ⟨a,ha,?_⟩
    funext i
    exact Fin.ext (show a (some i) = (v i).val from rfl)
  · intro a ha
    have hsum := (total a).mp ha
    change G (a none) _ = G (k-∑ i, a (some i)) _
    exact congrArg (fun t => G t (fun i => a (some i))) (by omega)
end
end ContinuumConstruction.MatchAllocation.PostedFieldDegreeAllocations

namespace ContinuumConstruction.MatchAllocation.PostedFieldSubstitution
open YM YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.Scale
open scoped Classical BigOperators
noncomputable section

theorem original {G : Gauge} {n h : ℕ} (Z : Guard G h) (T : ℕ → Structure1.Point G h n)
    (v : Fin n → Sec G h) (k : ℕ) :
    Dframe.status Z T k v = ∑ ν : Fin n → Fin (k+1),
      if (∑ i, (ν i).val) ≤ k then T (k-∑ i, (ν i).val)
        (fun i => (PowerSeries.coeff (ν i).val Z) (v i)) else 0 := by
  classical
  simpa only [Dframe.status, sum_apply, MultilinearMap.compLinearMap_apply] using
    PostedFieldDegreeAllocations.original (n:=n) (k:=k)
      (fun j ν => T j (fun i => (PowerSeries.coeff (ν i) Z) (v i)))
end
end ContinuumConstruction.MatchAllocation.PostedFieldSubstitution

namespace ContinuumConstruction.MatchAllocation.PostedCouplingPowers
open YM YM.MS YM.FVA2 YangMills.Matching Finset
open scoped BigOperators Classical
noncomputable section

theorem original (c : Book.Program.Cn) (f : ℕ → ℝ)
    (coefficients : ∀ k, PowerSeries.coeff k c = (f k : ℂ)) (j k : ℕ) :
    Book.Program.cut c j k = (couplingPower f j k : ℂ) := by
  induction j generalizing k with
  | zero => cases k <;> simp [Book.Program.cut, couplingPower]
  | succ j ih =>
    rw [Book.Program.cut, pow_succ', PowerSeries.coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a c * PowerSeries.coeff b (c ^ j)) k]
    rw [couplingPower, Complex.ofReal_sum, ← Fin.sum_univ_eq_sum_range (fun a => PowerSeries.coeff a c * PowerSeries.coeff (k-a) (c^j)) (k+1)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [coefficients, Complex.ofReal_mul]
    exact congrArg (fun z : ℂ => (f a.val : ℂ) * z) (ih (k-a.val))

end
end ContinuumConstruction.MatchAllocation.PostedCouplingPowers

namespace ContinuumConstruction.MatchAllocation.PostedThermalTruncation
open YM.MS Finset
open scoped BigOperators Classical
noncomputable section

theorem above (c : Book.Program.Cn) (zero : PowerSeries.coeff 0 c = 0)
    {j d : ℕ} (later : d < j) : Book.Program.cut c j d = 0 := by
  obtain ⟨u,rfl⟩ := PowerSeries.X_dvd_iff.mpr ((PowerSeries.coeff_zero_eq_constantCoeff_apply c).symm.trans zero)
  rw [Book.Program.cut, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (Nat.not_le.mpr later)]

theorem original (c : Book.Program.Cn) (zero : PowerSeries.coeff 0 c = 0)
    {T : Type*} [AddCommGroup T] [Module ℂ T] (A : ℕ → T) {d k : ℕ} (hd : d ≤ k) :
    (Book.Program.substitute c A) d = ∑ j : Fin (k+1), Book.Program.cut c j.val d • A j.val := by
  classical
  change ∑ j ∈ Iic d, Book.Program.cut c j d • A j =
    ∑ j : Fin (k+1), (fun j : ℕ => Book.Program.cut c j d • A j) j.val
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => Book.Program.cut c j d • A j) (k+1)]
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.mem_Iic.mp hj).trans hd))
  · intro j _ hj
    have late := Nat.lt_of_not_ge (fun h => hj (Finset.mem_Iic.mpr h))
    rw [above c zero late, zero_smul]
end
end ContinuumConstruction.MatchAllocation.PostedThermalTruncation

namespace ContinuumConstruction.MatchAllocation.PostedPhysicalConversionEntry
open YM YM.Integration YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2 YM.FVA2.Register YM.FVA2.Scale
open YM.XSpace YM.XSpace.Normalize YangMills.Matching
open scoped Classical BigOperators
noncomputable section

theorem original {G : Gauge} (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {S : Prescription (Press.portDeck G)} {simple : G.Simple} {dial : Bool}
    (matched : Main.Match Z simple M S dial) (μ : ℝ) (f : ℕ → ℝ)
    (coupling : ∀ i, PowerSeries.coeff i (Measure.f Z.criterion μ M) = (f i : ℂ))
    {n h : ℕ} (x : Stage n) (v : Fin n → Sec G h) (k : ℕ) :
    Measure.outlook Z.scheme Z.criterion h n x k v =
      ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
        if (∑ i, (ν i).val) ≤ k then (couplingPower f j.val (k-∑ i, (ν i).val) : ℂ) *
          Equator.wave μ M h n x j.val (fun i => (PowerSeries.coeff (ν i).val
            (Measure.Z Z.scheme Z.criterion μ M h)) (v i)) else 0 := by
  classical
  rw [← matched.eqconv μ h]
  change Dframe.status (Measure.Z Z.scheme Z.criterion μ M h)
    ((Book.Program.substitute (Measure.f Z.criterion μ M)) (Equator.wave μ M h n x)) k v = _
  rw [PostedFieldSubstitution.original]
  apply Finset.sum_congr rfl
  intro ν _
  split_ifs with within
  · have cut := PostedThermalTruncation.original (Measure.f Z.criterion μ M)
      (matched.positionCoupling μ).1.start (Equator.wave μ M h n x)
      (show k-∑ i, (ν i).val ≤ k from Nat.sub_le _ _)
    rw [cut]
    simp only [sum_apply, smul_apply, smul_eq_mul,
      PostedCouplingPowers.original _ f coupling]
  · simp
end
end ContinuumConstruction.MatchAllocation.PostedPhysicalConversionEntry

namespace ContinuumConstruction.MatchAllocation.PostedRealFiledCoupling
open YM YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2 YM.FVA2.Register YM.FVA2.Scale
noncomputable section
variable {G : Gauge} (Z : WilsonPrescription G)
    (raw : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {S : Prescription (Press.portDeck G)} {simple : G.Simple} {dial : Bool}
    (matched : Main.Match Z simple raw S dial) (μ : ℝ)
def coefficient (k : ℕ) : ℝ := (PowerSeries.coeff k (Measure.f Z.criterion μ raw)).re
include matched in
theorem original :
    (∀ k, PowerSeries.coeff k (Measure.f Z.criterion μ raw) = (coefficient Z raw μ k : ℂ)) ∧
    coefficient Z raw μ 0 = 0 ∧ coefficient Z raw μ 1 = 1 := by
  let c := Measure.f Z.criterion μ raw
  have tangent := (matched.positionCoupling μ).1
  refine ⟨?_,?_,?_⟩
  · intro k
    have conjugate : (starRingEnd ℂ) (PowerSeries.coeff k c) = PowerSeries.coeff k c := by
      simpa only [PowerSeries.coeff_map] using (congrArg (PowerSeries.coeff k) tangent.real)
    have imaginary := congrArg Complex.im conjugate
    simp only [Complex.conj_im] at imaginary
    apply Complex.ext
    · rfl
    · change (PowerSeries.coeff k c).im = 0
      linarith
  · unfold coefficient
    rw [show PowerSeries.coeff 0 (Measure.f Z.criterion μ raw) = 0 from tangent.start]
    rfl
  · unfold coefficient
    rw [tangent.lead]
    rfl
end
end ContinuumConstruction.MatchAllocation.PostedRealFiledCoupling

noncomputable section
namespace YM.Answer.ContinuumLimit
open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Entree Future
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped BigOperators Classical ContDiff Topology
universe u
variable {G:Gauge}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}
variable {ξ:Extraction.Order} {V:Vision E ξ} {Z:WilsonPrescription G}{dial:Bool} {Q:Perspective H Z dial}

namespace SourceOnlyGraphSum
open _root_.ContinuumConstruction.MatchAllocation
open YangMills.Matching

/-- The bare graph values at common grade h, after applying the measured field series at
each insertion's own grade and the real signed coupling series at the nominated datum. -/
def screen (Z : WilsonPrescription G) (A : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (μ : ℝ) {n h : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → Sec G (d i))
    (within : ∀ i, d i ≤ h) (x : Scale.Stage n) (k : ℕ) : ℂ :=
  ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
    if (∑ i, (ν i).val) ≤ k then
      (couplingPower (PostedRealFiledCoupling.coefficient Z A μ) j.val (k-∑ i,(ν i).val) : ℂ) *
      YM.MS.Graphical.separatedGraphSum μ G h x.val j.val (fun i => XSpace.Normalize.up (within i)
        ((PowerSeries.coeff (ν i).val (Measure.Z Z.scheme Z.criterion μ A (d i))) (v i))) else 0

def EveryCoefficient (Z : WilsonPrescription G) (A : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (μ : ℝ) : Prop :=
  ∀ {n h : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → Sec G (d i))
    (within : ∀ i, d i ≤ h) (x : Scale.Stage n) (k : ℕ),
      Jury.fxt (Measure.outlook Z.scheme Z.criterion h) x.val k
        (fun i => XSpace.Normalize.up (within i) (v i)) = screen Z A μ d v within x k

theorem atMatch (Z : WilsonPrescription G) (A : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} (matched : Main.Match Z H A σ dial) (μ : ℝ) :
    EveryCoefficient Z A μ := by
  intro n h d v within x k
  have bare (j : ℕ) : YM.MS.Graphical.separatedGraphSum μ G h x.val j = Equator.wave μ A h n x j :=
    YM.MS.Graphical.identification_screen μ A x.property
  have caps (i : Fin n) (j : ℕ) :
      (PowerSeries.coeff j (Measure.Z Z.scheme Z.criterion μ A h)) (XSpace.Normalize.up (within i) (v i)) =
        XSpace.Normalize.up (within i) ((PowerSeries.coeff j (Measure.Z Z.scheme Z.criterion μ A (d i))) (v i)) :=
    matched.frameCompat μ (d i) h (within i) j (v i)
  rw [Jury.fxt, dif_pos x.property]
  have physical := PostedPhysicalConversionEntry.original Z A matched μ
    (PostedRealFiledCoupling.coefficient Z A μ) (PostedRealFiledCoupling.original Z A matched μ).1
    x (fun i => XSpace.Normalize.up (within i) (v i)) k
  simpa only [screen, bare, caps] using physical

/-- One nominated subtraction datum and one physical election serve every reference scale,
mixed-grade roster, separated point and coefficient of the measured series. -/
theorem nominated (V : Vision E ξ) (Z : WilsonPrescription G)
    (A : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (lamp : Bool) :
    ∃ Q : Perspective H Z lamp, Q.MS = A ∧ Vision.StandaloneCorrelation V Z A ∧
      ∀ μ : ℝ, EveryCoefficient Z A μ := by
  obtain ⟨Q, hQ⟩ := compared H Z lamp A
  refine ⟨Q,hQ,hQ ▸ Vision.standaloneFromActualField V Q,?_⟩
  intro μ
  have matched := Q.matching
  rw [hQ] at matched
  intro n h d v within x k
  exact atMatch Z A matched μ d v within x k
end SourceOnlyGraphSum
end YM.Answer.ContinuumLimit
