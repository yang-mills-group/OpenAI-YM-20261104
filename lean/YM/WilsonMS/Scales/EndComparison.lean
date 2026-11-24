import YM.WilsonMS.Scales.NearPort
/-!
# X-Space to MS-bar

`PoseEnd`: The correlation end theorem. In particular:

* `calibration`, `flavor`: parameter and compensating finite matrices,
  a log-independent convention at μ=1 (see `ClockH` for signs). `Z` and the
  mass-independent adjustment `shiftAll` fixed for all applications.
* `transferred`, `rescaled`: dilation relation in check and M schemes.
* `vertices`: the MS point amplitudes, after applying the **same** coupling
  composition and label transformation, give the Wilson/X-space points.
* `tested`, `efficient`: on all compact-position and smooth supported
  tests the limits are power accurate at the regulators.

`Delivered` in this file retains the information about the generating
finite-regulator PT before taking these limits, so these arrays can be
related to the rest of Wilson Prescription.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Network
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Plane MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice TraceMC GFlow
  Datum
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
variable (W : Initialize G) {V : Store G} (Y : Rose.Pick V)

structure PoseEnd (W : Initialize G) {V : Store G} (Y : Rose.Pick V) {M : Booked (Ensure.deck G)}
    (F : MS_Data G M) (f : Cn) (Z : Links G) : Prop where
  runsOut : Ends W Y (forecast W Y) (report W Y)
  checkPack (d : ℕ) : GFlow.Marked (check W Y d) (checked W Y d)
  grain (d : ℕ) : CloseP (Z d)
  rope : Aware f
  calibration : PowerSeries.subst f (FrameConj.χMS 0 Y F) = PowerSeries.X
  flavor (d : ℕ) : Z d = coupon f (deck (Gates.Lμ V F 0 d)) * shiftAll W Y d
  homogeneous (d : ℕ) : Mass (Z d)
  nested : Connect Z
  vertices (d : ℕ) : Equad (Act (GFlow.Sub f (GMS F 0 d)) (Z d)) (check W Y d)
  erected (d : ℕ) : Anchored (mandates W Y) (shiftAll W Y d)
  reference_scale (s : ℝ) : Linked (forecast W Y) s ((mandates W Y).Q s) ((mandates W Y).r s)
  coherent_N : Connect (shiftAll W Y)
  transferred (t : ℝ) :
    let C := mandates W Y;
    let B : Links G := fun d => compass t (C.r t) (C.Q t d) (shiftAll W Y d)
    Linked (check W Y) t B (C.r t)
  rescaled (s : ℝ) : Linked (GMS F 0) s (frameMS Y F s) (muFlow Y F s)
  charged (s : ℝ) : PowerSeries.subst f (muFlow Y F s) = f.subst ((mandates W Y).r s)
  intertwines :
    PowerSeries.subst f (Beta (muFlow Y F)) = PowerSeries.derivative ℂ f * Beta (mandates W Y).r
  compatible (d i : ℕ) : recruit (step d) (checked W Y (d + 1) i) = checked W Y d i
  efficient (j d : ℕ) : NShape (fun i => tilings W Y d i j) (checked W Y d j)
  tested (d j n : ℕ) (v : Fin n → Sec G d) (K : Set (Points n)) (ht : IsCompact K) (hK : K ⊆ conf n) :
    Vitals (fun i => tilings_pt W Y d i j v) (fun x => check W Y d n x j v) K
  uniqueness (p : Cn) (T : Links G) (hp : Aware p) (he : ∀ i, CloseP (T i)) :
    (∀ d, Equad (Act (GFlow.Sub p (GMS F 0 d)) (T d)) (check W Y d)) → p = f ∧ T = Z
namespace PoseEnd

lemma permit (g : G.Simple) {M : Booked (Ensure.deck G)} {F : MS_Data G M}
    {A : Prescription (Ensure.deck G)} (h : Installed W F A) (hp : Commuting A) :
    PoseEnd W Y F (ψW Y F) (Zx Y F) := by
  obtain H := obtains W Y g F h hp
  have he := ψ_aware Y g h hp
  have hX := adjusts W Y g F h hp
  have ht := MAN W Y g F h hp
  refine
    ⟨testifies W Y g F h hp, end_reads W Y g F h hp, neutral Y g h hp, he, (awareχ Y g h hp 0).undo,
      fun i => ?_, fun _ => Mass.print, cnZ Y F, fun d => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun p T hv hQ hx => ?_⟩
  · rw [hX]
    exact congr_fun (recallZ Y g h hp) i
  · rw [← Ck Y g h hp]
    exact Equad.symm (sameCheck W Y g F h hp d)
  · rw [hX, ht]
    exact grade_N Y g h hp
  · intro i
    rw [ht]
    exact starts H.2 (growth Y g h hp) i
  · rw [hX]
    exact cN Y g h hp
  · intro i
    rw [ht, hX]
    exact starts (fun d => sameCheck W Y g F h hp d) (kinetic Y g h hp) i
  · exact Earnings Y g h hp
  · intro s
    rw [ht]
    exact scaleMS_f Y g h hp s
  · rw [ht]
    exact identity_β Y g h hp
  · exact step_check W Y g F h hp
  · intro j d
    exact ranges W Y g F h hp d j
  · intro i j n
    exact wound W Y g F h hp i j
  exact (Υtest Y g h hp hv hQ (fun i => (hx i).trans (sameCheck W Y g F h hp i))).symm

lemma walking {M : Booked (Ensure.deck G)} {F : MS_Data G M} {f Z} (h : PoseEnd W Y F f Z) (K : Run)
    (j d n : ℕ) (t : Test n) (p : Fin n → Sec G d) :
    Tendsto (fun i => tilings W Y d (K.step i) j n t p) atTop
      (𝓝 (realm (Z d) (substitute f (fun i => Continuum F 0 i d)) j n t p)) := by
  rw [←
    show checked W Y d = realm _ _ from
      Marked.unique (h.checkPack d) (T := Act (GFlow.Sub f (GMS F 0 d)) (Z d))
        (fun i => pivotFund (FundSwim (coupon_stage F 0 d i) _) _) ((h.vertices d).symm)]
  exact (((h.efficient j d).eval p t).limit).comp (Cirrus.goesFront (Stretched.runs K))
end PoseEnd
section theory

def continuum (G : Gauge) : MS_Data G (JRad.book G) :=
  Classical.choice (Land.bookedMS _)
open MS.Fleet MS.Swirl MS.Vista MS.Rake MS.Tide MS.Orbit

variable {I X : Type} [LinearOrder X]

structure Delivered (G : Gauge) (F : MS_Data G (JRad.book G)) (V : Store G) (Y : Rose.Pick V)
    (W : Initialize G) (A : Prescription (Ensure.deck G)) : Prop where
  lettering : Commuting A
  mark_present : Installed W F A
  source_read (X I : Type) (_ : LinearOrder X) (J : MS.Dial.Trial I X) (h : Removed.safe J)
    (p : X → Label (Ensure.deck G)) (i : I) (K : Finset X) :
    PhysicalSum G A.team (J.profile.η i) (dimT J.side i) true K (fun w => J.off w i) (J.head i)
      (fieldSeries W (Near.Stripped A.team) A p) (Fleet.bury i K (BMenu.tagD W J h A p))
  exact_branch (μ : ℝ) (d : ℕ) :
    ∀ᶠ i in Front,
      coupon (Program.shift A.team (μ - height i)) (deck (V.layout W i d)) =
        bets A (μ - height i) (height i) d *
          deck ((V.survey d).Lays (V.prepared d) (amended W μ A i d))
  speed_mark (d j : ℕ) : NShape (fun i => Rose.proposed W Y i d j) (report W Y d j)
  match_chart : PoseEnd W Y F (ψW Y F) (Zx Y F)

lemma deliver {A} (g : G.Simple) (F : MS_Data G (JRad.book G)) (h : Installed W F A)
    (hp : Commuting A) : Delivered G F V Y W A :=
  ⟨hp, h, fun _ _ _ _ _ _ _ _ => BMenu.on_m W _ _ _ _ _ _, fun μ d => exact_breg μ V g h hp d,
    by
    intro d j
    rw [obtains W Y g F h hp |>.1]
    exact removing Y W A F 0 g h hp j d, PoseEnd.permit W Y g h hp⟩

noncomputable def doctrine (G : Gauge) (h : G.Simple) : Store G :=
  Classical.choice (Normalize.equipped h)

noncomputable def tester (G : Gauge) (h : G.Simple) (W : Initialize G) (V : Store G) : Rose.Pick V :=
  Classical.choice (Rose.nominate W h V)
omit [LinearOrder X]

lemma presented (h : G.Simple) : ∃ A, Delivered G (continuum G) V Y W A := by
  obtain ⟨A, hA, hh⟩ := Rider.Equipped W (continuum G) h
  exact ⟨A, deliver W Y h _ hh hA⟩

theorem running (G : Gauge) (g : G.Simple) :
    let W := Initialize.standard G;
    let V := doctrine G g;
    let T := tester G g W V;
    ∃ A, Delivered G (continuum G) V T W A := by
  intro W V T
  exact presented W T g
end theory
end YM.WilsonMS.Network
