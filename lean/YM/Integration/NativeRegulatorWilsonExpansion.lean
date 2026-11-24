import YM.Integration.NativeRegulatorFirstBlock
import YM.Integration.NativeWilsonBlockExpansion
import YM.Integration.NativeWilsonBlockObservable
import YM.Comparison.RG02.Step.History

/-! Actual finite Wilson integrals and their complete asymptotic expansions
on the genuine first block selected by the moving regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeRegulatorWilsonExpansion

open Function Filter Lattice Wilson Precision RG Labels PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal
open PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2
open Integral Exterior Arm Marker Multi Pipeline Pipeline.See Period.Field Sound
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement NativeFormalRegulatorCollector
open WilsonLimitConstruction.FundedFormalEconomy NativeFormalDiagonalCollector PowerSeries
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {hG : G.Simple} {W : Bank R hG} {μ : ℝ}
  {P : MS.Land.Prescription (nativeDeck R)} {Z : branches R}
  {C : Lodge.Contract R (program R) Z} {A : table R} {g : G.ColorIndex}
  {I : Type} [Fintype I] [DecidableEq I] {i : I} {S : Marker.Census I}
  (T : Trial W μ P Z C A g i S)

local notation "𝓑" => C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)
local notation "periodSystem" => Period.Field.LodgeT.instance_real (program R) Z R C
  (schedule Z C T.order) (above Z C T.order)
local notation "𝓛" => Calibration.sheet T.calibrate
local notation "σ" => T.stop T.station

variable {n : ℕ} (v : Pegs.Motor (C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)) n T.station)
  (d : Fin n → ℕ) (u : (a : Fin n) → (R.family.labels.level (d a)).Index)
local notation "𝓐" => T.stamp.traces T.station n σ v d u
local notation "𝓕" => Figure.prop R (ProgramT.spend (program R) Z R C
  (schedule Z C T.order) (above Z C T.order) T.location T.station n v) d u
variable (j : ℕ) (x : fieldDir G (R.family.side (NativeRegulatorInitialDatum.level T j) (T.stop T.station)) 1)
local notation "step₀" => NativeRegulatorInitialDatum.first T j
local notation "Y₁" => (periodSystem).records (𝓑).desk R.family.path σ (step₀).next
local notation "L₁" => T.stamp.menu.cloth (step₀).next
local notation:max "data₀" a:max => NativeRegulatorInitialDatum.datum T v d u j a
open Comparison.RG02.Moving.Path


open Comparison.RG02.Laplace
local notation "Y" => RunFormalChain.fromRun R
local notation "m₀" => NativeRegulatorInitialDatum.level T j
local notation "Δ₀" => R.family.path.levels.clock.op m₀ σ
local notation "V₁" => R.family.path.rep (m₀+1) σ m₀
local notation "τ₀" => Pert.Asymptotics.regulatorRun R.family (m₀+1) σ (m₀+1)
local notation:max "prime₁" y:max => See.prime periodSystem S i 𝓛 σ T.order T.stamp.menu 𝓐 (x := (step₀).next) y
local notation:max "visible₁" q:max y:max => See.visible S (Y₁).clip (Y₁).path L₁ (𝓐 (step₀).next) q y

private theorem witnessed {G : Gauge} (Q : Run G) {V : Type} [DecidableEq V] [Fintype V]
    (H : Marker.Census V) (b : V) {l : ℕ} (B : Boot.Scout (G := G) l) (D : LocalFormal.Datum Q.family H)
    (hN : D.cutoff = D.level+1) (hB : D.colors = Boot.ink H b Q.family.path (D.level+1) D.period B) :
    Bare.Witnessed D.colors (D.kernel (RunFormalChain.fromRun Q)) := by
  rcases D with ⟨N,p,m,h,F,t,V,x⟩
  dsimp only at hN hB ⊢
  subst N
  subst V
  exact Boot.Revenue.receiving Q p m H B b

/-- Actual Wilson-weighted, tagged, gauge-averaged nonlinear block integral
at freely varying positive coupling on this fixed selected lattice. -/
def moment (t : ℝ) : Marker.Poly S :=
  Bare.realMoment ((data₀ x).kernel Y) (data₀ x).forest (data₀ x).colors (data₀ x).tag x t

private theorem certified : Bare.Witnessed (data₀ x).colors ((data₀ x).kernel Y) :=
  witnessed R S i (𝓕 j) (data₀ x) (NativeRegulatorInitialDatum.cutoff T v d u j x)
    (NativeRegulatorInitialDatum.colors T v d u j x)

/-- Full finite physical expansion of all ordinary and connected marker
partitions and the scalar vacuum on the exact initial datum of this Trial. -/
theorem ensemble : Fleet.Test ((data₀ x).raw Y T.order) (moment T v d u j x) ∧
    Laplace.Trial (Laplace.detail ((data₀ x).vacuumLog Y T.order) S.quiet)
      (fun t => Complex.ofReal (Real.log (Bare.rho ((data₀ x).kernel Y) (data₀ x).forest (data₀ x).tag x t))) T.order ∧
    Fleet.Test ((data₀ x).ordinary Y T.order) (fun t => Order.unitScale (moment T v d u j x t)) ∧
    Fleet.Test ((data₀ x).markedLog Y T.order) (fun t => Extra.Trajectories.connected (Order.unitScale (moment T v d u j x t))) :=
  Bare.wilson_step_test ((data₀ x).kernel Y) (data₀ x).forest (data₀ x).colors (data₀ x).tag
    x T.order (R.family.path.levels.budget m₀) (certified T v d u j x)

/-- The outgoing marked observable is the genuine normalized Wilson expansion
at the inserted physical field, to the whole requested horizon. -/
theorem marked : Laplace.Trial (prime₁ x)
    (fun t => (Order.unitScale (moment T v d u j x t)).part (S.fire i)) T.order :=
  Laplace.trial_flow ((ensemble T v d u j x).2.2.1 (S.fire i))
    (fun k hk => (NativeRegulatorFirstBlock.marked T v d u j x k hk).symm)

private theorem normalized_at {G : Gauge} (Q : Run G) {V : Type} [DecidableEq V] [Fintype V]
    (H : Marker.Census V) (b : V) {l : ℕ} (B : Boot.Scout (G := G) l) (D : LocalFormal.Datum Q.family H)
    (hN : D.cutoff = D.level+1) (hB : D.colors = Boot.ink H b Q.family.path (D.level+1) D.period B)
    (t : ℝ) (ht : 0 < t) :
    (Order.unitScale (Bare.realMoment (D.kernel (RunFormalChain.fromRun Q)) D.forest D.colors D.tag D.field t)).part (H.fire b) =
      (NativeWilsonBlockExpansion.density (Q.family.path.levels.clock.op D.level D.period) D.field t)⁻¹ •
      NativeWilsonBlockObservable.numerator (Q.family.path.levels.clock.op D.level D.period) B D.field t := by
  rcases D with ⟨N,p,m,h,F,o,V,x⟩
  dsimp only at hN hB ⊢
  subst N
  subst V
  exact NativeWilsonBlockObservable.normalized Q H b m p B F o x t ht

/-- The original physical matrix insertion at the exact conditional Wilson
density. Its native engineering power remains inside the fine integral. -/
def observable (t : ℝ) : ℂ :=
  (NativeWilsonBlockExpansion.density Δ₀ x t)⁻¹ • NativeWilsonBlockObservable.numerator Δ₀ (𝓕 j) x t

theorem conditional (t : ℝ) (ht : 0 < t) :
    (Order.unitScale (moment T v d u j x t)).part (S.fire i) = observable T v d u j x t :=
  normalized_at R S i (𝓕 j) (data₀ x) (NativeRegulatorInitialDatum.cutoff T v d u j x)
    (NativeRegulatorInitialDatum.colors T v d u j x) t ht

theorem physical_mark : Laplace.Trial (prime₁ x) (observable T v d u j x) T.order :=
  Laplace.trial_congr (eventually_pos.mono (fun t ht => conditional T v d u j x t ht))
    (marked T v d u j x)

def logarithm (t : ℝ) : ℂ :=
  Complex.ofReal (Real.log (NativeWilsonBlockExpansion.density Δ₀ x t)) -
  Complex.ofReal (Real.log (NativeWilsonBlockExpansion.density (G := G) Δ₀ 0 t))

/-- The centered outgoing marked-program action is the full nonlinear Wilson
log-density response at this field at every order of the selected Trial. -/
theorem vacuum : Laplace.Trial (fun k => visible₁ k x) (logarithm T j x) T.order :=
  Laplace.trial_flow (NativeWilsonBlockExpansion.centered ((data₀ x).kernel Y) (data₀ x).forest
    (data₀ x).colors (data₀ x).tag x T.order (R.family.path.levels.budget m₀) (certified T v d u j x))
    (fun k hk => (NativeRegulatorFirstBlock.vacuum T v d u j x k hk).symm)

theorem unique_mark (a : ℕ → ℂ) (h : Laplace.Trial a
    (fun t => (Order.unitScale (moment T v d u j x t)).part (S.fire i)) T.order) :
    ∀ k ≤ T.order, prime₁ x k = a k :=
  Laplace.trial_gap (marked T v d u j x) h

theorem unique_observable (a : ℕ → ℂ) (h : Laplace.Trial a (observable T v d u j x) T.order) :
    ∀ k ≤ T.order, prime₁ x k = a k :=
  Laplace.trial_gap (physical_mark T v d u j x) h

theorem unique_vacuum (a : ℕ → ℂ) (h : Laplace.Trial a (logarithm T j x) T.order) :
    ∀ k ≤ T.order, visible₁ k x = a k :=
  Laplace.trial_gap (vacuum T v d u j x) h

/-- The physical value at the Run's own positive coupling. -/
theorem density_at :
    NativeWilsonBlockExpansion.density Δ₀ x τ₀ = (V₁).eval (Integral.sample τ₀ x) := by
  unfold NativeWilsonBlockExpansion.density
  rw [Local.RealStep.trajectory R.family (m₀+1) σ (m₀+1) R.makes le_rfl]
  rw [show (V₁).eval = (Δ₀).push (R.family.path.rep (m₀+1) σ (m₀+1)).beta
    (R.family.path.rep (m₀+1) σ (m₀+1)).eval from (R.makes.wilson.steps (m₀+1) σ m₀ (Nat.lt_succ_self _)).1,
    show (R.family.path.rep (m₀+1) σ (m₀+1)).eval = Wilson.bare (R.family.path.rep (m₀+1) σ (m₀+1)).beta
      from (R.makes.wilson.starts (m₀+1) σ).2]

theorem logarithm_at : logarithm T j x τ₀ =
    Complex.ofReal (Real.log ((V₁).eval (Integral.sample τ₀ x))) - Complex.ofReal (Real.log ((V₁).eval 1)) := by
  unfold logarithm
  rw [density_at T j x, density_at T j 0]
  simp [Integral.sample]

/-- One constant covers both signed physical outputs after fixing the
lattice, cutoff, field, observable and order. -/
theorem bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ t : ℝ in Laplace.along,
    ‖observable T v d u j x t - peval (prime₁ x) T.order t‖ ≤ M*t^(T.order+1) ∧
    ‖logarithm T j x t - peval (fun k => visible₁ k x) T.order t‖ ≤ M*t^(T.order+1) := by
  obtain ⟨a,ha,h₁⟩ := physical_mark T v d u j x
  obtain ⟨b,_,h₂⟩ := vacuum T v d u j x
  refine ⟨max a b,ha.trans (le_max_left _ _),?_⟩
  filter_upwards [h₁,h₂,eventually_pos] with t ht hs hpos
  exact ⟨ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hpos.le _)),
    hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hpos.le _))⟩

end YM.Integration.NativeRegulatorWilsonExpansion
end
