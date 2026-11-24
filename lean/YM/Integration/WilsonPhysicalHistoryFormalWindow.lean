import YM.Integration.WilsonPhysicalHistoryFormalReturn
import YM.Integration.WilsonPhysicalHistoryBoundary
import YM.Integration.WilsonWindowFormalAnnouncement
import YM.FormalBulk08.Trellis.Arch

/-! The numerical cost of the original independent normalized inverse over
the actual growing window on the already selected cutoff run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFormalWindow

open Filter Real Function Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep WilsonPhysicalHistoryFormalReturn
open WilsonPhysicalExteriorMeshStops Next.Foundations RG16.Literal RG16.Guarding IterationFour.Currency
open scoped Classical BigOperators Matrix Topology

variable {G : Gauge}

/-- Bound both genuine geometric inputs of the historical inverse theorem
in the reporting clock of the first physical crossing. -/
theorem geometry (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c : ℝ} (hc : c≤2) :
    ∀ᶠ k : ℕ in atTop, let z := RG16.Lambda R.family.path.levels k
      2≤z ∧ max 1 (ageZ (R.family.path.levels.clock.hatBeta k)) ≤ z ∧
      R.family.S.scale (ultraviolet R.family c k)-R.family.S.scale k ≤ 3*z^2 := by
  let A := R.family.path.levels
  filter_upwards [(lambda_leads R.family simple).eventually_ge_atTop 3,
    ultraviolet_window R.family simple slow.2 c] with k large window
  let z := RG16.Lambda A k
  change 3≤z at large
  have one : 1≤z := by linarith
  have pos : 0<log (A.clock.hatBeta k) := by change 3≤2+log (A.clock.hatBeta k) at large; linarith
  have age : ageZ (A.clock.hatBeta k) ≤ z := by
    have r := Real.log_le_sub_one_of_pos pos
    change 1+log (log (A.clock.hatBeta k)) ≤ 2+log (A.clock.hatBeta k)
    linarith
  have twop : 0<log 2 := log_pos (by norm_num)
  have twou : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have zp : 0<log (z+log 2) := log_pos (by linarith)
  have os : log (log (z+log 2)) ≤ z := by
    have r := log_le_sub_one_of_pos zp
    have j := log_le_sub_one_of_pos (show 0<z+log 2 by linarith)
    linarith
  have power : z^c ≤ z^(2:ℕ) := by
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le one hc
  have total : R.family.S.scale (ultraviolet R.family c k)-R.family.S.scale k ≤ z^c + log (log (z+log 2)) := window.2.2
  change 2≤z ∧ max 1 (ageZ (A.clock.hatBeta k))≤z ∧ _
  exact ⟨by linarith,max_le one age, by nlinarith [mul_nonneg (sub_nonneg.mpr one) (show 0≤z by linarith)]⟩

/-- Finite observations on the real scale window, with independent lower
and upper cutoffs of the formal vacuum. -/
structure Reading (C : Family G) (c : ℝ) (K : ℕ) where
  base : ℕ
  finish : ℕ
  lower : ℕ
  upper : ℕ
  late : K≤base
  forward : base≤finish
  inside : finish≤ultraviolet C c base
  valid : finish≤lower
  nested : lower≤upper

def clock (C : Family G) (c : ℝ) (K : ℕ) : Time (Reading C c K) :=
  ⟨fun x=>RG16.Lambda C.path.levels x.base, fun x=>by linarith [lambda_up C x.base]⟩

variable (R : Run G) {d D : ℕ} (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G) (depth : d<D)

def inverseAt (N i j : ℕ) :=
  Trellis.ropes (day R L a N) (matrix R L a depth N) i i (j-i)

/-- Put the true return in either reporting endpoint clock before multiplication. -/
def inverseAtClock (last : Bool) (N i j : ℕ) :=
  Trellis.ropes (day R L a N) (matrix R L a depth N) (if last then j else i) i (j-i)

/-- The original independently normalized inverse entries are polynomially
bounded in the measured physical log clock uniformly through the first
growing window. Two arbitrary finite vacuum cutoffs have the prescribed
discounted coefficient difference, on that very same selected run. -/
theorem pricedAt (last : Bool) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {U : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical U R.kit)
    (o : Loc G 1) {c : ℝ} (hc : c≤2) (E : ℕ) :
    ∃ K : ℕ, ∀ x y : Letter (R.family.labels.level d), ∀ e≤E,
      Pact (clock R.family c K) (fun t=> ratioR R.family.S t.lower t.finish targetPower)
        (fun t=>coeff e (inverseAtClock R L a depth last t.lower t.base t.finish x y))
        (fun t=>coeff e (inverseAtClock R L a depth last t.upper t.base t.finish x y)) := by
  let C := R.family
  let J := d+D+E+5
  have j5 : 5≤J := by dsimp [J]; omega
  have jd : d+3≤J := by dsimp [J]; omega
  have jD : D≤J := by dsimp [J]; omega
  have jE : E≤J := by dsimp [J]; omega
  obtain ⟨K,gates⟩ := eventually_atTop.mp
    ((C.path.levels.fits.deep.eventually_ge_atTop J).and (geometry R simple slow hc))
  have JK : J≤C.path.levels.clock.J (K+1) := (gates (K+1) (Nat.le_succ K)).1
  let W := First.cbook (C:=C) L K (Primer.FamilyWindow C) (Borough.lyre C.path.levels)
  let ann := WilsonWindowFormalAnnouncement.on_run R grant
  have poster : Borough.Poster (Primer.Noise C) Spigot.herald C.labels.level C.params (chart G) W J :=
    Borough.presold simple (W:=Primer.FamilyWindow C) (U:=W.toEmpire) (fun _=>ann.power)
      W.neck j5 (fun _=>JK)
  let q := poster.spare d D o J E jd depth jD le_rfl jE
  let Q := Reading C c K
  let n (t : Q) := t.finish-t.base
  let V : Voyage W n :=
    { bed := fun t=>⟨PUnit.unit,t.base,t.late⟩
      summit := fun t=>t.lower
      top := fun t=>t.upper
      extra := fun t=>t.nested
      high := fun t=> by change t.base+(t.finish-t.base)≤t.lower; have:=t.forward; have:=t.valid; omega }
  let τ := clock C c K
  have adult : Soft τ (fun t=>(chron _).day (V.bed t)) := by
    apply (soft_day τ).below
    intro t
    change |max 1 (ageZ (C.path.levels.clock.hatBeta t.base))| ≤ |RG16.Lambda C.path.levels t.base|
    rw [abs_of_nonneg (zero_le_one.trans (le_max_left ..)),abs_of_pos (lambda_pos C _)]
    exact (gates _ t.late).2.2.1
  have close (t : Q) : t.base+n t=t.finish := by dsimp [n]; have:=t.forward; omega
  have width : Soft τ (fun t=>sowing (W.V (V.bed t).a).S (V.bed t).b ((V.bed t).b+n t)) := by
    refine ⟨3,2,by norm_num,?_⟩
    intro t
    change |C.S.scale (t.base+n t)-C.S.scale t.base| ≤3*(RG16.Lambda C.path.levels t.base)^2
    rw [close,abs_of_nonneg (sub_nonneg.mpr ((OPE.scale_mono C.S).monotone t.forward))]
    exact (sub_le_sub_right ((OPE.scale_mono C.S).monotone t.inside) _).trans (gates _ t.late).2.2.2
  let T := C.localSection d
  let f (t : Q) := t.base
  let reportAt (t : Q) := if last then t.base+n t else t.base
  have endpoint : (∀ t,reportAt t=(V.bed t).b) ∨ (∀ t,reportAt t=(V.bed t).b+n t) := by
    cases last with
    | false => exact Or.inl fun _=>rfl
    | true => exact Or.inr fun _=>rfl
  have pricedEntries := Trellis.chiro (T:=T) q (poster.vac _ jE) (chart_ok _) a simple
    (ann.available.sections d) (ann.inputs d) (show d≤J by omega) V f n
    (fun _=>le_rfl) (fun _=>le_rfl) adult width reportAt endpoint
  have rho : R.metals.O = chart G := grant.1
  have band (N : ℕ) : bandK (chart G) a W (fun _=>N) PUnit.unit = day R L a N := by
    funext i
    unfold day
    rw [rho]
    rfl
  have row (N : ℕ) :
      Elm.bornM (ρ:=chart G) (W:=W) (T:=T) a q.horizon PUnit.unit N = matrix R L a depth N := by
    calc
      _ = Elm.bornM (ρ:=R.metals.O) (W:=W) (T:=T) a q.horizon PUnit.unit N :=
        congrArg (fun v=>Elm.bornM (ρ:=v) (W:=W) (T:=T) a q.horizon PUnit.unit N) rho.symm
      _ = _ := rfl
  let endAt (t : Q) : Lengths n := ⟨t,n t,le_rfl⟩
  refine ⟨K,?_⟩
  intro x y e he
  have receipt := (pricedEntries x y e he).link endAt
  change Pact τ (fun t=>ratioR C.S t.lower (t.base+n t) targetPower)
    (fun t=>coeff e (Trellis.ropes (bandK (chart G) a W (fun _=>t.lower) PUnit.unit)
      (Elm.bornM (ρ:=chart G) (W:=W) (T:=T) a q.horizon PUnit.unit t.lower) (reportAt t) t.base (n t) x y))
    (fun t=>coeff e (Trellis.ropes (bandK (chart G) a W (fun _=>t.upper) PUnit.unit)
      (Elm.bornM (ρ:=chart G) (W:=W) (T:=T) a q.horizon PUnit.unit t.upper) (reportAt t) t.base (n t) x y)) at receipt
  simpa only [reportAt,close,band,row,inverseAtClock,n,τ,C] using receipt

/-- Start-coordinate specialization used when transporting source data from the reporting stage. -/
theorem priced (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {U : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical U R.kit)
    (o : Loc G 1) {c : ℝ} (hc : c≤2) (E : ℕ) :
    ∃ K : ℕ, ∀ x y : Letter (R.family.labels.level d), ∀ e≤E,
      Pact (clock R.family c K) (fun t=>ratioR R.family.S t.lower t.finish targetPower)
        (fun t=>coeff e (inverseAt R L a depth t.lower t.base t.finish x y))
        (fun t=>coeff e (inverseAt R L a depth t.upper t.base t.finish x y)) := by
  simpa only [inverseAtClock,Bool.false_eq_true,if_false,inverseAt] using
    pricedAt R L a depth false simple slow grant o hc E

end YM.Integration.WilsonPhysicalHistoryFormalWindow

