import YM.FVAAlt2.Triangle
import YM.MS.Dial.Signals
/-!
# Literal Wilson LPT readings on a library of lit marks.

One `Library` takes the role of the actual `LitBook` reader *before* any geometry
or perturbative order/list: expose exactly the chosen stencils on all periods.
Obtainable in principle from ANY LitBook--`Witness` can be constructed with that data.
It can also be constructed with the actual stencils, not leaving an equivalence to solve
post-hoc (but attaching those from the actual history/dictionary remains separate).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Billing
open MS MS.Koszul MS.Native MS.Native.Wilsonian MS.Native.Studio MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Puff MS.Puff.Actors MS.Swirl MS.Puff.Mom Swirl.Near MS.Fleet MS.Menus
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog Convolve Program MS.Rake MS.Tide MS.Local.Physical MS.Dial
open Function Finset Filter Topology MeasureTheory Lattice SchemeRG11.Sway SchemeRG11.Sway.Lam Pert.Orb
open Precision PertExtension Ends AtomCert
open scoped PowerSeries ContDiff
variable {G:Gauge}{n:Side}{d:ℕ}{W:Type}[LinearOrder W]
variable {B:MS.Local.Physical.Deck G} (Z: LitBook B) (P:ChartRatio G) (p:W→Label B)
set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-- each glyph refers to **same** field for its size and slot number, not
separate realizations for higher horizons -/
structure Library (Z: LitBook B) where
  final (d r:ℕ)(i:B.BIndex d r)(n:Side): Wilson.Config G n →ℝ
  ok(d r:ℕ)(i:B.BIndex d r)(n:Side) (x: Site n): AtomCert x (Z.stamp d r i) r (moveLetter x (final d r i n))
lemma always_L(Z:LitBook B) : Nonempty (Library Z):=by choose f hf using fun d k i (n:Side)=> AtomCert.supplied (n:=n) (Z.stamp d k i) (Z.levels d k i); exact ⟨⟨f,hf⟩⟩

variable (Λ:Library Z)(K:MS.Land.Prescription B)(m:Finset W)(v:W→Cover)(A:Cover)(y:ℝ)

local notation "g" => fun i:W=> (p i).h -- quot
local notation "ℱ"=> ApplyM Z ( Stripped K.team ) K p
abbrev χ (p:W→Label B)(i:W):=Glyph B ((p i).h)
def Ζ (i:W)(j:χ p i):= Z.stamp j.size j.grade j.2.2
def guide (n:Side)(i:W)(j:χ p i):= moveLetter (wrap n (A+v i)) (Λ.final j.size j.grade j.2.2 n)
def bore (i:W)(j:χ p i):= PowerSeries.mk (fun k=> oil (K.fees (g i) (p i).item) j k y)
def ΓReg (n:Side) : PowerSeries ℂ := treeReg m K.team y (fun i (k:χ p i)=> k.grade) (guide Z p Λ v A n) (bore p K y) (fun i=> MS.Land.read (p i).item) P

lemma lampBill(i:W) : ℱ i y=∑ j:χ p i, scalS (bore p K y i j) (substitute (shift K.team y) (Book.levels j.grade (Ζ Z p i j))) := by
 funext k; change Menus.rent Z _ _ y k= _; unfold Menus.rent; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun w _=> ?_ ; unfold scalS Glyph.preamble; rw [strip_wobble]; unfold bore; rw [paired]; simp_rw [unpack,PowerSeries.coeff_mk]; rfl

lemma spectrum (hn:Admissible n)(hp: LocalRatio P): PhysicalSum G K.team y n true m v A ℱ (unpack (ΓReg Z P p Λ K m v A y n)) := by
  letI hpL : Module.Free ℝ (Land G n):= Module.Free.of_divisionRing ℝ (SchemeRG11.Sway.Land G n)
  let L:=Module.finBasis ℝ (SchemeRG11.Sway.Land G n); let R:=Module.finBasis ℝ (ScalarGhost G n)
  refine PayReg hp  L R ℱ m K.team y v A (Ζ Z p) (fun i (k:χ p i)=> k.grade) (guide Z p Λ v A n) (bore p K y) (fun i (j:Glyph B (g i))=> Λ.ok j.size j.grade j.2.2 n (wrap n (A+v i))) (fun i=> MS.Land.read (p i).item) (lampBill Z p K y) ?_ ?_ hn -- get order
  -- symmetry etc
  · intro i k; exact (billRent Z (Stripped K.team) (K.fees (g i) (p i).item) |>.actual k y).symm -- suffix typing
  intro i j; change ∃ k,Limit (Menus.rent Z _ _ _ _).val k; exact ⟨_, Menus.rentLimit Z (Stripped K.team) _ y j ⟩
end YM.FVAAlt2.Billing
