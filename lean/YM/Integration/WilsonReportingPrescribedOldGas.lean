import YM.Integration.WilsonReportingPrescribedOldReturn
import YM.Integration.WilsonAllDateHarvestPropagation
import YM.RG05Readout.Many.Film

/-! The recorded Many reference and the independently enrolled Q program at one
nonbare reporting scale. The entire signed old forced partition is evaluated
before either source is integrated at any earlier scale. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingPrescribedOldGas
open Function Finset Lattice Wilson RG Source Marker Multi Extra.Histories RG05Readout RG05Readout.Many
open RG05Readout.Address MergeProof Accent Menu MergeProof.Replicums RG3.Held RG3.Script.Picnic
open Labels FVA1 PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Extraction Table Spec RG12 RG17 MS MS.Menus MS.Local.Physical
open WilsonAllDateHarvestPropagation
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V] (J : Census V)

/-- The original quiet Wilson gas and every singly marked old forced activity
use the same set of actual occupied flags in this finite signed sum. -/
def forced (P : Rep G n) (rows : V → Three G n) (W : Config G n) : Poly J :=
  field (fun p => bar P.activities J W p + Mach J (fun v => profile P.activities (rows v).2.2 p W))
    (flags P.p.threshold W)

/-- The full difference that has to enter the old conditional. The
prescription is compared with the actual regular row on this same field. -/
def residual (P : Rep G n) (rows : V → Three G n) (X : V → Config G n → ℂ) (W : Config G n) : Poly J :=
  (Real.exp (P.exponent W) : ℂ) •
    (Poly.pass (Mach J (fun v => (rows v).2.1 W)) *
      (forced J P rows W - (P.activities.gas P.p W : ℂ) •
        Poly.pass (Mach J (fun v => X v W - (rows v).2.1 W))))

theorem compared (P : Rep G n) (rows : V → Three G n) (X : V → Config G n → ℂ) (W : Config G n) :
    density (J:=J) P rows 0 0 W - birth J P X W = residual J P rows X W := by
  let a := Mach J (fun v => (rows v).2.1 W)
  let b := Mach J (fun v => X v W - (rows v).2.1 W)
  have add : a+b = Mach J (fun v => X v W) := by
    unfold a b Mach
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [← YM.Multi.send_add]
    congr 1
    ring
  have product : Poly.pass a * Poly.pass b = Poly.pass (Mach J (fun v => X v W)) :=
    (Next.Rank.Exponential.pass_add a b (mute J _) (mute J _)).symm.trans (congrArg Poly.pass add)
  unfold density restore birth residual
  simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero]
  change (Real.exp (P.exponent W) : ℂ) • (Poly.pass a * forced J P rows W) -
    (P.eval W : ℂ) • Poly.pass (Mach J (fun v => X v W)) =
    (Real.exp (P.exponent W) : ℂ) • (Poly.pass a * (forced J P rows W -
      (P.activities.gas P.p W : ℂ) • Poly.pass b))
  rw [mul_sub,smul_sub,Algebra.mul_smul_comm,product,smul_smul,Rep.eval,Complex.ofReal_mul]

/-- Every mode licensed by the original Many census has a coefficient in
the independently filed full Q stock. -/
theorem admitted : J.choices ⊆ (Stock.census V).choices := fun i _ => Finset.mem_univ i

variable (R : Run G) {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S)
  (L : Layout F) {B : Deck G} (Q : MS.Land.Prescription B)
variable [Nonempty V]

theorem original (hG : G.Simple) (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
    (r : ℝ) (hr : 0 < r) (N per : ℕ) (live : L.level r < N) {n : ℕ} {hn : n ≤ L.level r}
    (D : ActualRunQlocalNativeTuple.Datum R per (L.level r) n hn V)
    (age : ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ L.level r)
    (z : V → Site (R.family.side N per))
    (placed : ∀ i, (R.family.S.toDepth live.le per).parent (z i) = ActualRunQlocalNativeTuple.root D i)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (rows : V → Three G (R.family.side (L.level r) per)) (U : Config G (R.family.side (L.level r) per)) :
    density (J:=J) (R.family.path.rep N per (L.level r)) rows 0 0 U -
      narrow (admitted J) (((ActualOriginalQInput.input Q D u μ orders hG N live.le).leaf x).density U) =
      residual J (R.family.path.rep N per (L.level r)) rows
        (fun i W => ActualRunQlocalNativeTuple.reader D i (x i) *
          WilsonReportingPrescribedOldReturn.column R F L r live Q (u i) μ (orders i) (z i) W) U := by
  rw [WilsonReportingPrescribedOldReturn.original R F L r live Q hG u μ orders hr D age z placed x U,
    birth_choice]
  exact compared ..

end YM.Integration.WilsonReportingPrescribedOldGas
