import YM.Integration.WilsonCapturedPrimaryWardFullIntake
import YM.Integration.WilsonOriginalFiledIntrinsicInvoices

/-! The physical singleton entries and the entire multiply occupied income on
one dated Wilson representative, in the units of the full original stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardOwnedIntake
open Filter Finset Function MeasureTheory Lattice Wilson RG Source Labels Push
open Extra.Histories Extra.Trajectories Extra.Multi RG05Readout Native Address
open PhysicalNext.Repeat Legato RG17 Bandage Stock RG12 Records Copper
open MergeProof MergeProof.Accent Push.Local Marker
open WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetTale
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open WilsonCapturedPrimaryWardFullIntake WilsonCapturedPrimaryActiveArms
open WilsonCapturedPrimaryWardAppointment WilsonCapturedPrimaryWardEnrolled
open WilsonThermometerMarchSource
open scoped Classical Topology BigOperators
set_option quotPrecheck false

variable {G:Gauge} (R:Run G) {n k N p:ℕ} (d:Fin n→ℕ) (o:Fin n→Site (R.family.side N p))
variable (S:Shelf (N:=N) (p:=p) R k d o) (y:(i:Fin n)→Palette R.family (d i))
local notation "J" => Stock.census (Fin n)
local notation "homes" => WilsonThermometerOwnOffsetJoint.origins R o
local notation "repAt" => R.family.path.rep N p
local notation "secAt" => R.family.localSection
local notation "D" => WilsonThermometerIntrinsicRoster.density R d o (trimmed R d y) S.route J
local notation "s₀" => (fun j i=>state (k:=k) R (S.viewer i) (S.route i) (trimmed R d y i) (o i) j)
local notation "s₁" => (fun j i=>state (k:=k) R (S.viewer i) (S.route i) (y i) (o i) j)

theorem physical (i:Fin n) (j:ℕ) :
    (charge (y i):ℂ) • s₀ j i=s₁ j i:=by
  dsimp only [state]
  split_ifs
  · simp only [moved,strand,trimmed,reduce,map_smul,LinearMap.smul_apply]
    rw [smul_comm (WilsonThermometerOwnOffsetNectar.factor R k j (d i)),smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (charged (y i)).ne'),one_smul]
  · exact smul_zero _

def Owned (t:ℕ) (v:(i:Fin n)→R.family.label (d i)) : Prop :=
  ∀ j (_:k≤j) (hj:j≤N),
    ∃ q : (i:Fin n) → Coefficient (R.family.labels.level (d i)) (R.family.side j p),
      (∀ i,(q i).Format (homes j i) R.family.params (repAt j) ∧
        (q i).remBound (homes j i) (repAt j) (kappa R.family.path j) (radius R t k j/charge (y i))⁻¹ ∧
        invoice (q i) (homes j i) (secAt (d i)) (repAt j)=s₁ j i ∧
        ∀U,(q i).density (homes j i) (secAt (d i)) (repAt j) U=(full R d o v hj U).part ((J).fire i)) ∧
      Served (repAt j) (fun i=>(q i).exponentialEntry (homes j i) (secAt (d i)) (repAt j))
        (fun i=>profile (repAt j).activities (q i).forced) (full R d o v hj) (homes j)
        (fun i=>radius R t k j/charge (y i)) (topPitch R.family.path N j) 1

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap t:ℕ) (positive:1≤t):∀ᶠ k:ℕ in atTop,∀{N p n:ℕ} (live:k≤N) (d:Fin n→ℕ) (_:∀i,d i≤cap)
    (o:Fin n→Site (R.family.side N p)) (S:Shelf (N:=N) (p:=p) R k d o) (v:(i:Fin n)→R.family.label (d i))
    (y:(i:Fin n)→Palette R.family (d i)),Fine t S live v y→Owned R d o S y t v:=by
  filter_upwards [WilsonOriginalFiledIntrinsicInvoices.received R simple shop cap t positive] with k offered N p n live d bounded o S v y fine
  have issued:=offered live d bounded o S.viewer S.route S.receipt (Stock.census (Fin n)) (trimmed R d y)
    (fun i=>WilsonThermometerMarchSource.small (y i)) fine.1
  intro j kj jN
  let P:=R.family.path.rep N p j
  let origins:=WilsonThermometerOwnOffsetJoint.origins R o j
  let sec:=R.family.localSection
  let c (i:Fin n):ℂ:=charge (y i)
  obtain ⟨Q,good,served⟩:=issued j kj jN
  have reprice:=WilsonCapturedPrimaryWardCarton.original (fun i=>charge (y i)) (fun i=>charged (y i)) P served
  rw [undo R d o S live v y fine jN] at reprice
  have witness (i:Fin n):invoice (stretch (c i) (Q i)) (origins i) (sec (d i)) P=c i • invoice (Q i) (origins i) (sec (d i)) P:=
    invoice_stretch ..
  have smooth (i:Fin n):(stretch (c i) (Q i)).exponentialEntry (origins i) (sec (d i)) P=
      c i • (Q i).exponentialEntry (origins i) (sec (d i)) P:=
    congrArg (fun x:Three G (R.family.side j p)=>x.2.1) (witness i)
  have hard (i:Fin n):profile P.activities (stretch (c i) (Q i)).forced=c i • profile P.activities (Q i).forced:=
    profile_scale ..
  refine ⟨fun i=>stretch (c i) (Q i),fun i=>?_,?_⟩
  · obtain ⟨fmt,bill,read⟩:=good i
    have trueRead:=witness i
    rw [read,physical] at trueRead
    refine ⟨stretch_format _ fmt,?_,trueRead,?_⟩
    · have cost:=stretch_rem (c i) bill
      rw [show ‖c i‖=charge (y i) from by dsimp [c];rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (charged (y i))]] at cost
      simpa only [div_eq_mul_inv,mul_inv,inv_inv,mul_comm] using cost
    · intro U
      have mono:=(fine.1 j kj jN).2.1 i
      have before:=congrFun mono U
      have f₀:=congrArg (fun x:Three G (R.family.side j p)=>x.2.1) read
      have k₀:=congrArg (fun x:Three G (R.family.side j p)=>x.2.2) read
      change (Q i).exponentialEntry (origins i) (sec (d i)) P=_ at f₀
      change (Q i).forced=_ at k₀
      dsimp only [manifest] at before
      rw [←f₀,←k₀] at before
      change _= (Q i).density (origins i) (sec (d i)) P U at before
      rw [stretch_density,←before,←congrFun (undo R d o S live v y fine jN) U]
      rw [WilsonCapturedPrimaryWardFiring.names_part,Poly.toll]
      simp [Census.fire,c]
  · change Served P (fun i=>(stretch (c i) (Q i)).exponentialEntry (origins i) (sec (d i)) P)
      (fun i=>profile P.activities (stretch (c i) (Q i)).forced) _ _ _ _ _
    rw [funext smooth,funext hard]
    exact reprice

end YM.Integration.WilsonCapturedPrimaryWardOwnedIntake
