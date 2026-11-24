import YM.Integration.WilsonCapturedPrimaryWardRoster
import YM.Integration.WilsonCapturedPrimaryWardThermometer

/-! Install the actual projected microscopic fields on the same earned source
routes. The finite named table retains the quiet factor and all proper faces
after each genuine conditional push. Only the occupied source charges appear. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardAppointment
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open scoped Classical Topology
set_option quotPrecheck false
open WilsonThermometerIntrinsicRoster
open WilsonCapturedPrimaryActiveArms Extra.Trajectories
open scoped BigOperators
variable {G : Gauge} (R : Run G) {N p k n : ℕ}
variable (d : Fin n → ℕ) (z : Fin n → Site (R.family.side N p))
variable (v : (i:Fin n) → R.family.label (d i)) (y : (i:Fin n) → Palette R.family (d i))
variable (r : (i:Fin n) → Emblems R.family (d i))
local notation "C" => R.family

def input (names : Census (Fin n)) : Config G ((C).side N p) → Poly names :=
  Accent.birth names ((C).path.rep N p N) (fun i=>(C).O N p (v i) (z i))

def share (i : Fin n) : ℂ := ((WilsonThermometerMarchSource.charge (y i) : ℝ):ℂ)⁻¹
abbrev trimmed (i : Fin n) : Palette (C) (d i) := WilsonThermometerMarchSource.reduce (y i)

lemma leaf (live : k ≤ N) (named : WilsonCapturedPrimaryNamedReturn.primary R (p:=p) d r live v y) (i : Fin n) :
    WilsonThermometerIntrinsicRoster.source R d z (trimmed R d y) r live i =
      share R d y i • (C).O N p (v i) (z i) := by
  let a : ℂ := ((C).S.a k:ℂ)^(d i)
  have alive : a ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ((C).S.a_pos k).ne')
  have chosen : ((C).factory (d i) N p).terminal (finer (r i) live (trimmed R d y i) (primaryLetter (d i))) =
      share R d y i • (a⁻¹ • v i) := by
    rw [trimmed,WilsonThermometerMarchSource.reduce,map_smul,Pi.smul_apply]
    exact (((C).factory (d i) N p).terminal.map_smul (share R d y i)
      (finer (r i) live (y i) (primaryLetter (d i)))).trans
        (congrArg ((share R d y i) • ·) (named i))
  unfold WilsonThermometerIntrinsicRoster.source WilsonThermometerOwnOffsetNectar.birth
  rw [chosen]
  change a • ((C).O N p (share R d y i • (a⁻¹ • v i)) (z i)) = share R d y i • ((C).O N p (v i) (z i))
  have linear := (C).linearO N p (d i) (z i)
  rw [linear.map_smul (share R d y i) (a⁻¹ • v i),linear.map_smul (a⁻¹) (v i),smul_smul,smul_smul]
  congr 1
  rw [mul_right_comm, mul_inv_cancel₀ alive, one_mul]

lemma paid (names : Census (Fin n)) :
    Integrable (input R d z v names) (prior G _) := by
  have quiet : Continuous ((C).path.rep N p N).eval := by
    have starts : ((C).path.rep N p N).eval=bare ((C).beta N p) := (R.makes.wilson.starts N p).2
    rw [starts]
    exact bare_cont _
  exact (hatCont (C) N p (fun i=>(C).O N p (v i) (z i))
    (fun i=>(C).continuousO N p (d i) (v i) (z i)) quiet names).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma whole (live : k ≤ N) (names : Census (Fin n))
    (named : WilsonCapturedPrimaryNamedReturn.primary R (p:=p) d r live v y) (s : names.Mode) :
    (fun U=>(Accent.birth names ((C).path.rep N p N)
      (WilsonThermometerIntrinsicRoster.source R d z (trimmed R d y) r live) U).part s) =
      (∏ i∈s.val,share R d y i) • (fun U=>(input R d z v names U).part s) := by
  funext U
  have here (i:Fin n) := congrFun (leaf R d z v y r live named i) U
  simp only [Accent.birth,Accent.Mach,input,Poly.part_smul,pass_fire,Pi.smul_apply,smul_eq_mul,here]
  rw [Finset.prod_mul_distrib]
  ring

theorem posted (live:k≤N) (names:Census (Fin n))
    (named : WilsonCapturedPrimaryNamedReturn.primary R (p:=p) d r live v y)
    (admitted : Integrable (WilsonThermometerIntrinsicRoster.density R d z (trimmed R d y) r names live (le_refl N)) (prior G _))
    (s:names.Mode) {i:ℕ} (under:i≤N) :
    (fun U=>(WilsonThermometerIntrinsicRoster.density R d z (trimmed R d y) r names live under U).part s) =
      (∏ j∈s.val,share R d y j) •
        (fun U=>(gust (C).path N p N (input R d z v names) i under U).part s) := by
  unfold WilsonThermometerIntrinsicRoster.density at admitted
  rw [gust_base] at admitted
  exact WilsonThermometerMarchFaceTransport.restored (C) _ _ s _ admitted (paid R d z v names)
    (whole R d z v y r live names named s) under

/-- A single paid exponent and date before the actual passport and the amplitude. -/
theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) (D : ℕ) :
    ∃ t ≥ D+3, ∀ᶠ k : ℕ in atTop, ∀ N p (hk:k≤N) (n:ℕ) (d:Fin n→ℕ)
    (_:∀i,d i≤D) (z:Fin n → Site ((C).side N p)),
    (∀ i j:Fin n,i≠j → ((C).path.levels.budget k).B^2 <
      separation (WilsonThermometerOwnOffsetJoint.origins R z k i)
        (WilsonThermometerOwnOffsetJoint.origins R z k j)) →
    ∀ (S : Shelf (N:=N) (p:=p) R k d z) (names : Census (Fin n))
      (v:(i:Fin n)→(C).label (d i)) (y:(i:Fin n)→Palette (C) (d i)),
      WilsonCapturedPrimaryNamedReturn.primary R (p:=p) d S.route hk v y →
      WilsonThermometerIntrinsicRoster.filed R d z (trimmed R d y) S.viewer S.route names hk t ∧
      ∀ i (under:i≤N) (s:names.Mode),
        (fun U=>(WilsonThermometerIntrinsicRoster.density R d z (trimmed R d y) S.route names hk under U).part s) =
          (∏ j∈s.val,share R d y j) • (fun U=>(gust (C).path N p N (input R d z v names) i under U).part s) := by
  obtain ⟨t,dt,issued⟩ := WilsonCapturedPrimaryWardRoster.original R simple shop D
  refine ⟨t,dt,?_⟩
  filter_upwards [issued] with k dates
  intro N p hk n d cap z room S names v y named
  have filed := dates p N hk (Fin n) d cap z room S.viewer S.route S.receipt names
    (trimmed R d y) (fun i=>WilsonThermometerMarchSource.small (y i))
  refine ⟨filed,?_⟩
  exact fun i under s=>posted R d z v y S.route hk names named (filed N hk le_rfl).1 s under

end YM.Integration.WilsonCapturedPrimaryWardAppointment
