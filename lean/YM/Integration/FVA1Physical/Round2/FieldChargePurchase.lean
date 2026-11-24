import YM.Integration.FVA1Physical.Round2.PhysicalCurrentCharge
import YM.Integration.FVA1Physical.Round2.FieldWordTrajectory

/-! Purchase the marked chart invoice on the same calibrated run as the
independent forest. Its price is smaller than an arbitrary fixed power of
inverse coupling on every admitted period, with independent test fields. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG YM.Wilson Source Labels Extra.Histories Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Roof Push.PriceCompiler
open Next.Foundations UVNext.CouplingReset Graces Roost Qlocal.Schedule
open Push.Local Push.AbsoluteSums LocalLTE Further.LogJets Push.Uniform
open Integration.FVA1Physical.Marked RGComparison.Core16.Spool MSbar MSbar.Lis MSbar.Heath MSbar.Midpoint MSbar.Rolling MSbar.Whisk
open MSbar.Heath.Stock MSbar.Mosaic
open scoped Classical BigOperators Topology
variable {G : Gauge} {I : Type} [Fintype I] {d : ℕ}

private theorem charge_gate_exists (a : I → CoverLabel G d) (H H' : Stage) (q s radius : ℕ)
    {δ : ℝ} (pos : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      (0 < αm x ∧ (((s:ℝ)+1)*αm x+2*αm x)*q*(6*(⌈hatW x⌉₊:ℝ)+2) ≤ H.supportExponent) ∧
      wordSupportFare G q s x * ((2:ℝ)^q*chartFactor G q*fieldShelf a H' radius) ≤ x^δ := by
  have h := (support_fare_subpower G q s).mulY tendsto_id ((2:ℝ)^q*chartFactor G q*fieldShelf a H' radius)
  filter_upwards [eventual_field_width q s H.price_pos,h δ pos] with x width fare
  exact ⟨width,(le_abs_self _).trans fare⟩

def chargeGate (a : I → CoverLabel G d) (q s radius : ℕ) {δ : ℝ} (pos : 0 < δ) : StageThreshold :=
  fun H H' _ _ => (eventually_atTop.mp (charge_gate_exists a H H' q s radius pos)).choose

abbrev LateThreshold (R : PhysicalNext.Repeat.Legato.Run G) (f : StageThreshold) : Prop :=
  ∀ᶠ k : ℕ in atTop, ∀ j, k ≤ j → ∀ n,
    f (R.alloy.B.a.params j) (R.alloy.B.a.params (j+1)) (R.alloy.B.a.clock.op j n).patch
      (R.alloy.B.a.clock.op j n).kernel ≤ R.alloy.B.a.clock.hatBeta j

theorem purchased_current_charge (R : PhysicalNext.Repeat.Legato.Run G) (hG : G.Simple)
    (V : Voice G) (clear : Clear G V) (a : I → CoverLabel G d) (q s radius : ℕ) (positive : 0 < q)
    {δ D : ℝ} (pos : 0 < δ) (hD : 0 ≤ D)
    (purchase : LateThreshold R (chargeGate a q s radius pos)) :
    ∀ᶠ k : ℕ in atTop, ∀ N n j, k ≤ j → j < N →
      let H := R.family.path
      let S := H.levels.clock.op j n
      let A := H.rep N n (j+1)
      let x := H.levels.clock.hatBeta j
      ∀ (b : Site (R.family.side j n)) (o : I → Site (R.family.side (j+1) n)),
        (∀ i, separation (o i-S.ratio.embed b) 0 ≤ radius) →
        ∀ (part : Bool) (Z : List (Primary (R.family.side j n) G) → Positions (Primary (R.family.side j n) G)),
          (∀ l, ‖Z l‖ ≤ D) →
          let f := fun z => Bulk.expect S A (postcard G (R.family.side j n) (cue A.beta) z)
            (fun U => look part (tally (freshLamps a) o U))
          fieldCharge (Measuring.chart (R.family.side j n) G) b (αm x) s q Z f ≤ x^δ := by
  let H := R.family.path
  let c := H.levels.clock
  have grow := (MSbar.Alto.broad.comp (Multi.Wage.hat_tend hG H.levels)).eventually_ge_atTop
    ((radius+LocalLTE.Vault.terr G d:ℕ):ℝ)
  obtain ⟨warm,wg⟩ := eventually_atTop.mp grow
  filter_upwards [purchase,regular_field_domain hG R V clear D hD,eventually_ge_atTop warm,
    eventually_ge_atTop (R.t 0),eventually_ge_atTop (R.t q),
    Finset.univ.eventually_all.mpr (fun i (_ : i ∈ (Finset.univ : Finset I)) => eventually_ge_atTop (R.t (a i).1.val))]
    with k bought domain cut start advanced ready N n j kj hj
  intro H' S A x b o foot part Z inside f
  have stages := R.T.choice.represents N n j hj.le
  have fine := R.T.choice.represents N n (j+1) hj
  let B := (H.rep N n j).p
  have out : B = H.levels.budget j := stages.vac
  have fit : radius+LocalLTE.Vault.terr G d ≤ A.p.B := by
    rw [show A.p=H.levels.budget (j+1) from fine.vac]
    exact Nat.cast_le.mp ((wg (j+1) (by omega)).trans (Nat.le_ceil _))
  have bills := (eventually_atTop.mp (charge_gate_exists a (H.levels.params j) (H.levels.params (j+1))
    q s radius pos)).choose_spec x (bought j kj n)
  have order : q ≤ B.order := by
    rw [out]
    exact (Nat.le_succ q).trans (((R.makes.stages q).2 j (advanced.trans kj)).1)
  refine (current_charge_on R hG hj (start.trans kj) a
    (fun i => (ready i (mem_univ i)).trans (by omega)) b o part radius q s positive Z foot fit
    (fun l => domain N n j kj hj (Z l) (inside l)) order bills.1.1 ?_).trans bills.2
  change (((s:ℝ)+1)*αm x+2*αm x)*q*(6*B.B+2:ℝ) ≤ B.supportExponent
  rw [out]
  exact bills.1.2

end YM.Integration.FVA1Physical.Round2.Curvature
