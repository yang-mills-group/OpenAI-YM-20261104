import YM.Integration.WilsonInvariantActionLogarithmicGeometry
import YM.Integration.WilsonMatrixTicketLanesReflectedFields

/-! The actual enrolled finite incoming stencils inherit the separation of each contributing physical test cell. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedSites
open Function Filter Set Finset Real Lattice Gauge RG Wilson Source Marker Extraction Spec
open Next.Rank PhysicalNext.Repeat.Legato RG17 FullVolume Extraction.Order RGComparison.Core16 RGComparison.Core16.Spool
open WilsonInvariantActionSeparatedCells Table Climb Trace.Pilot Next.UVStress
open scoped Topology BigOperators Classical
variable {G : Gauge}

def spread (A : Unit→Lamp G):ℕ:=Finset.univ.sup fun i : Slice A=>Finset.univ.sup fun k : YM.Axis=>(i.2.1.val k).natAbs

private theorem localSite {n : Side} (A : Unit→Lamp G) (o : Site n) (i : Slice A) :
    separation o (legs A (fun _=>o) i).1 ≤ spread A := by
  let z:=i.2.1.val
  change separation o (wrap n z+o) ≤ spread A
  rw [show separation o (wrap n z+o)=separation 0 (wrap n z) by simpa only [zero_add] using separation_translate (0:Site n) (wrap n z) o]
  change pdist (0-wrap n z) ≤ spread A
  rw [zero_sub,pdist_neg]
  apply Finset.sup_le
  intro k _
  exact (Lattice.Corona.lap z k).trans ((le_sup (s:=univ) (f:=fun t : YM.Axis=>(z t).natAbs) (mem_univ k)).trans
    (le_sup (s:=univ) (f:=fun i : Slice A=>Finset.univ.sup fun t : YM.Axis=>(i.2.1.val t).natAbs) (mem_univ i)))

theorem shifted {n : Side} (A B : Unit→Lamp G) (o u : Site n) :
    ∀ i : Slice A,∀ j : Slice B,separation o u-(spread A+spread B) ≤ separation (legs A (fun _=>o) i).1 (legs B (fun _=>u) j).1 := by
  intro i j
  have a:=localSite A o i
  have b:=localSite B u j
  rw [separation_comm] at b
  have one:=separation_triangle o (legs A (fun _=>o) i).1 u
  have two:=separation_triangle (legs A (fun _=>o) i).1 (legs B (fun _=>u) j).1 u
  omega

variable (R : Run G) (simple : G.Simple)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

include simple in
private theorem space (Q : ℕ) : ∀ᶠ b : ℕ in atTop,(2+log (β b))^3+(Q:ℝ) ≤ (((A).budget (b+1)).B^8:ℕ) := by
  have heat:=Station.hat_rate (A) simple
  have rise:=tendsto_log_atTop.comp (heat.comp (tendsto_add_atTop_nat 1))
  filter_upwards [rise.eventually_ge_atTop (max 3 (Q:ℝ))] with b ready
  let t:=log (β (b+1))
  have hi:3 ≤ t:=(le_max_left ..).trans ready
  have load:(Q:ℝ) ≤ t:=(le_max_right ..).trans ready
  have mono : log (β b) ≤ t:=log_le_log (zero_lt_one.trans ((A).fits.delayed b))
    (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le (Nat.le_succ b))
  have D₀:0 ≤ 2+log (β b):=by linarith only [log_nonneg ((A).fits.delayed b).le]
  have t1:1 ≤ t:=by linarith only [hi]
  have room:(2+log (β b))^3 ≤ t^6:=by
    rw [show t^6=(t^2)^3 by ring]
    exact pow_le_pow_left₀ D₀ (by nlinarith only [mono,hi,mul_nonneg (sub_nonneg.mpr hi) (show 0 ≤ t+2 by linarith only [hi])]) _
  have cheap : (Q:ℝ) ≤ t^6:=load.trans (by simpa only [pow_one] using pow_le_pow_right₀ t1 (show 1 ≤ 6 by decide))
  have doubled : t^6+t^6 ≤ t^7:=by rw [show t^7=t^6*t by ring];nlinarith only [mul_nonneg (pow_nonneg (zero_le_one.trans t1) 6) (show 0 ≤ t-2 by linarith only [hi])]
  calc
    _ ≤ t^16:=((add_le_add room cheap).trans doubled).trans (pow_le_pow_right₀ t1 (by decide))
    _ = (t^2)^8:=by ring
    _ ≤ (((A).budget (b+1)).B^8:ℕ):=by change _ ≤ (↑(⌈t^2⌉₊^8:ℕ):ℝ);rw [Nat.cast_pow];exact pow_le_pow_left₀ (sq_nonneg t) (Nat.le_ceil _) _

/-- Every true upper placement contributing nonzero signed mass has the required separation
at its actual common parent, with the original stencils and one radius fixed before all upper dates. -/
theorem original (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (large : 17 ≤ B)
    (φ : Test 2) (A₀ A₁ : Unit→Lamp G) : let m:=WilsonMeasuredWindow.stop (A) simple B
    ∀ᶠ r in trail,∀b,b+1=m r → ∀ (hr : 0<r) N per (h : b+1 ≤ N) (x : Fin 2→Site (R.family.side N per)),
      WilsonExternalMeshMass.charge R.family (dilate hr φ) x≠0 →
      let o:=fun i=>(R.family.S.toDepth h per).parent (x i)
      ∃H:ℕ,(2+log (β b))^3 ≤ (H:ℝ) ∧ ∀i : Slice A₀,∀j : Slice A₁,
        H ≤ separation (legs A₀ (fun _=>o 0) i).1 (legs A₁ (fun _=>o 1) j).1 := by
  let m:=WilsonMeasuredWindow.stop (A) simple B
  obtain ⟨grows,_⟩:=WilsonFundedMeasuredWindow.all_radii R pace simple (B:=B) (by omega)
  obtain ⟨t,start⟩:=eventually_atTop.mp (space R simple (spread A₀+spread A₁))
  filter_upwards [grows.eventually_ge_atTop (t+1),WilsonInvariantActionLogarithmicGeometry.original R simple pace large φ]
    with r late paid b date hr N per h x live o
  change b+1=m r at date
  have b₀:t ≤ b:=by
    change t+1 ≤ m r at late
    rw [←date] at late
    exact Nat.le_of_succ_le_succ late
  have addressed (j : ℕ) (eq : j=m r) (hj : j ≤ N) : (((A).budget j).B^8:ℕ) ≤ gap R.family hj x:=by
    subst j;exact (paid hr N per hj x live).1
  have physical:=addressed (b+1) date h
  let D:=separation (o 0) (o 1)
  let W:=spread A₀+spread A₁
  have charged:(2+log (β b))^3+(W:ℝ) ≤ (D:ℝ):=(start b b₀).trans (Nat.cast_le.mpr physical)
  have positive:0 ≤ (2+log (β b))^3:=pow_nonneg (by linarith only [log_nonneg ((A).fits.delayed b).le]) _
  have enough : W ≤ D:=by exact_mod_cast (show (W:ℝ) ≤ D by linarith only [charged,positive])
  refine ⟨D-W,?_,shifted A₀ A₁ (o 0) (o 1)⟩
  rw [Nat.cast_sub enough];linarith only [charged]

end YM.Integration.WilsonMatrixTicketLanesConnectedSites
