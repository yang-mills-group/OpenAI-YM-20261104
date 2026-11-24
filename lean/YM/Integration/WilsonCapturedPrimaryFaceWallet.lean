import YM.Integration.WilsonCapturedPrimaryUnitWallet
import YM.Integration.WilsonCapturedPrimaryNamedReturn

/-! Pay only the occupied primary lifts of a physical subword. Its unused
places remain in the same room and carry their genuine displaced unit. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryFaceWallet
open Function Filter MeasureTheory Lattice Wilson RG Source Labels
open Extra.Histories Extra.Histories.Relay Extra.Trajectories Extra.Multi Overlay
open PhysicalNext.Repeat.Legato RG05Readout Native Address Many Records Harvest Copper
open MergeProof Accent Cells Push GridApprox
open WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {n k N p : ℕ}
local notation "C" => R.family

def branch : Bool → ℕ → ℕ
  | true, e => e
  | false, _ => 0

def pick {F : ℕ → Type*} {e : ℕ} (b : Bool) (a : F e) (blank : F 0) : F (branch b e) :=
  match b with
  | true => a
  | false => blank

def level (d : Fin n → ℕ) (s : Finset (Fin n)) (i : Fin n) := branch (decide (i ∈ s)) (d i)

def label {d : Fin n → ℕ} (s : Finset (Fin n)) (x : (i : Fin n) → (C).label (d i))
    (i : Fin n) : (C).label (level d s i) :=
  pick (F:=(C).label) (decide (i ∈ s)) (x i) ((C).refUnit 0)

theorem one_side {F : ℕ → Type*} {e : ℕ} (f : (d : ℕ) → F d → ℂ)
    (b : Bool) (a : F e) (blank : F 0) :
    f (branch b e) (pick b a blank) = if b then f e a else f 0 blank := by
  cases b <;> rfl

inductive IsUnit (F : Family G) : (e : ℕ) → F.label e → Prop
  | atZero : IsUnit F 0 (F.refUnit 0)

private theorem size_one {e : ℕ} {x : (C).label e} (hz : IsUnit C e x)
    {V : Sight C e p} {r : Emblems C e} (z : Site ((C).side N p))
    (entry : Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R)
      k N p e (WilsonThermometerOffsetResidue.digits R N p z) V r)
    (kn : k ≤ N) (started : (C).ref 0 ≤ N) (y : Palette C e)
    (named : ((C).factory e N p).terminal (finer r kn y (primaryLetter e)) =
      (((C).S.a k:ℂ)^e)⁻¹ • x) : size y = 1 := by
  cases hz
  simp only [pow_zero, inv_one, one_smul] at named
  rw [WilsonCapturedPrimaryUnitWallet.original R z entry kn started y named]
  exact size_ticket _

theorem field (d : Fin n → ℕ) (s : Finset (Fin n))
    (x : (i : Fin n) → (C).label (d i)) (z : Fin n → Site ((C).side N p))
    (started : (C).ref 0 ≤ N) :
    WilsonCapturedPrimaryNamedReturn.field R (level d s) (label R s x) z =
      fun U => ∏ i ∈ s, (C).O N p (x i) (z i) U := by
  funext U
  have val (i : Fin n) : (C).O N p (label R s x i) (z i) U =
      if i ∈ s then (C).O N p (x i) (z i) U else 1 := by
    have pair := one_side (F:=(C).label) (fun j a => (C).O (d:=j) N p a (z i) U)
      (decide (i ∈ s)) (x i) ((C).refUnit 0)
    trans if decide (i ∈ s) then (C).O N p (x i) (z i) U
      else (C).O N p ((C).refUnit 0) (z i) U
    · exact pair
    · simp [(C).constant R.makes 0 started (z i)]
  simp [WilsonCapturedPrimaryNamedReturn.field,val]

theorem original (d : Fin n → ℕ) (s : Finset (Fin n))
    (x : (i : Fin n) → (C).label (d i)) (z : Fin n → Site ((C).side N p))
    (V : (i : Fin n) → Sight C (level d s i) p) (r : (i : Fin n) → Emblems C (level d s i))
    (enrolled : WilsonCapturedPrimaryFiledArms.entered R (level d s) z (k:=k) V r)
    (kn : k ≤ N) (started : (C).ref 0 ≤ N) (y : (i : Fin n) → Palette C (level d s i))
    (named : WilsonCapturedPrimaryNamedReturn.primary R (p:=p) (level d s) r kn (label R s x) y) :
    WilsonCapturedPrimaryFiledArms.rent R (level d s) y =
      (∏ i ∈ s, (1 + size (y i))) * 2^(n-s.card) := by
  have price (i : Fin n) (off : i ∉ s) : size (y i) = 1 := by
    have blank (b : Bool) (hb : b = false) :
        IsUnit C (branch b (d i)) (pick (F:=(C).label) b (x i) ((C).refUnit 0)) := by
      subst b; exact IsUnit.atZero
    have unitAt : IsUnit C (level d s i) (label R s x i) := blank _ (by simpa using off)
    exact size_one R unitAt (z i) (enrolled i) kn started (y i) (named i)
  rw [WilsonCapturedPrimaryFiledArms.rent, ← Finset.prod_mul_prod_compl s]
  congr 1
  calc
    ∏ i ∈ sᶜ, (1 + size (y i)) = ∏ _ ∈ sᶜ, (2:ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [price i (Finset.mem_compl.mp hi)]
      norm_num
    _ = _ := by simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]

end YM.Integration.WilsonCapturedPrimaryFaceWallet
