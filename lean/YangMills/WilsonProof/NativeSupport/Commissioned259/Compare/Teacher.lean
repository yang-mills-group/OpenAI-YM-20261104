import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Pick
/-! # Conversion of the prescribed correlation and OPE coefficients

The matching identities apply the coupling and field substitutions before truncation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set MeasureTheory PowerSeries Asymptotics
open XSpace XSpace.Normalize XSpace.Structure1
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open FVA2.Scale O.Score O.Enh O.Canon Dframe O.Project
open scoped Topology BigOperators Classical
variable {G : Gauge} (N : WilsonPrescription G) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    {n m z : ℕ} {d : Fin n → ℕ} {e : Fin m→ℕ} (hd : ∀ i,d i≤z) (he : ∀ i,e i≤z)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Z" => Scale.Measure.Z N.scheme N.criterion ν M
local notation "f" => Scale.Measure.f N.criterion ν M
local notation "Mx" => Equator.wave ν M
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν

/-- The wave with substitutions in the coupling and field variables, always
persists on the same h. All identities evaluated on the prescribed formal arrays. -/
abbrev convertedMS : Arenas G := fun k=> Facets.actMark (Z k) (Facets.couple f (Mx k))

/-- Pay OPE coefficients in **MS** on incoming Near labels with conversions Z and the
measure f, and convert back on through-h outputs, coefficientwise. Crop after making all these
substitutions. -/
abbrev MSfront (u : Slots G d) (x : Points n) (q : Q G) : PowerSeries ℂ :=
   ∑ b : BasisSlots G d, C (coordinates b u) *
     refund (seats Z) (seats (replay Z)) f (fun v=> FarCoefficients Mx v x) (names b) q

def purchaseMS (u : Slots G d) (x : Points n) (h p : ℕ) (t : ℝ) : Sec G h :=
  ∑ q : Toon G h, crop p t (MSfront N ν M u x (flash q)) • theory q

include H
lemma MSbook : Vx = convertedMS N ν M := funext fun k=>(H.eqconv ν k).symm
lemma MSmeasurement (u : Slots G d) (v : Slots G e) (x : Points n) (y : Points m) (t : ℝ) :
    measurement Vx B hd he x y t u v = measurement (convertedMS N ν M) B hd he x y t u v :=
  congr_arg (measurement · B hd he x y t u v) (MSbook N ν M H)
-- Apply the OPE matching identity coefficientwise at the original field labels.
lemma recited (u : Scan G n) (x : Points n) : FarCoefficients Vx u x =
    refund (seats Z) (seats (replay Z)) f (fun v=> FarCoefficients Mx v x) u := by
  have L := (H.separatedOPE ν); have hc : Civil Z := ⟨fun i=> (H.frame ν i).1, fun i=> (H.frame ν i).2,fun h => H.frameCompat ν _ _ h⟩
  have h := L.gifts u 0 x; unfold Gift at h
  change credit (seats Z) f (fun i=> OPECoefficients Mx i 0 x) u = _ at h
  rw [show (fun i: Scan G n=> OPECoefficients Mx i 0 x) = _ from funext (fun i=>congr_fun (L.continuum.start_u i) x),L.wilson.start_u] at h
  rw [refund,h,timely,spin_v hc,receipt_K]
lemma OPEMS (x : Points n) (u : Slots G d) (q : Q G) : farCf Vx u x q =
    MSfront N ν M u x q := by simp_rw [farCf,recited N ν M H]
lemma cropMS (x : Points n) (u : Slots G d) (h p : ℕ) (t : ℝ) : purchased Vx u x h p t =
    purchaseMS N ν M u x h p t := by simp_rw [purchased, OPEMS N ν M H, purchaseMS]
end YM.FVA2.GradedFar259.Comparing
