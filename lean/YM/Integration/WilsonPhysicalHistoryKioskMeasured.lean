import YM.Integration.WilsonPhysicalHistoryKioskInvoice
import YM.Integration.WilsonPhysicalHistoryKioskHeatOrder

/-! The actual signed change of the filed rough cumulant against the original
Wilson detector. One date pays all supports, physical cutoffs and periods. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskMeasured
open Function Finset Lattice Wilson RG Source Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface MeasureTheory WilsonPhysicalHistoryPictureRestore
open scoped Classical BigOperators

open Filter IterationFour PhysicalNext.Repeat.Legato Pert.Asymptotics OPE.Therm

/-- The date is independent of the physical cutoff, site, forest and period. -/
noncomputable def first {G : Gauge} (X : Run G) (simple : G.Simple)
    (thermal : OPE.Therm.Poetry X.family.path.levels) (divisions expense order : ℕ)
    {B ε : ℝ} (bn : 0≤B) (ep : 0<ε) : ℕ :=
  (eventually_atTop.mp (WilsonPhysicalHistoryKioskHeatOrder.spatial X simple thermal
    divisions expense order bn ep)).choose

variable {G : Gauge} {X : Run G}
local notation "C" => X.family
variable {I J V : Type} [Countable I] [Countable J] [DecidableEq V] [Fintype V]
  {per i N : ℕ} {L : Side}
  {x e f r s κ w b₀ b₁ z Y Γ K : ℝ} {T : Type} {A₀ : Teller G}
  {Q : ConnectedActivityE6.Target G A₀} {horizon : ConnectedActivityE6.Target.Order G w}
variable {tube : Pressure.Tube G (X.family.path.levels.clock.op i per)} (cash : Cash w x κ L Q horizon z tube (X.family.path.rep N per (i+1)))
  {k : ℕ} (eyes : Eyes cash (X.family.path.rep N per i) e Γ Y K k) (W : Travel.Walk cash (X.family.path.rep N per i) e f r s)
  {R : Census V} {o : V → Site (X.family.side (i+1) per)} (A : Gallery T I o (X.family.path.rep N per (i+1)) R)
  (previous : Lamps T J G (X.family.path.rep N per (i+1)).p o R) (weights : V → ℝ)
  (grant : Seal (picture A previous) weights b₀ b₁) (positive : ∀ v, 0 < weights v)
  (slots : HasSlots (X.family.path.rep N per (i+1)).p (X.family.path.rep N per (i+1)).activities) (cap : ∀ mode : R.Mode, mode.val.card ≤ k)
  (fits : 2*(b₀+b₁) ≤ K) (pin : T) (ω : V → ℝ) (pos : ∀ v,0 < ω v)
  {a q h : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid ω (X.family.path.rep N per (i+1)).p.B (a+2) q) (hard : A.K.Paid ω (X.family.path.rep N per (i+1)).p.B a h)

open QuadraticLocal.Shelter WilsonPhysicalHistoryKioskFirst
open WilsonPhysicalHistoryKioskGas WilsonPhysicalHistoryKioskRetained

private abbrev rows {T₀ I₀ V₀ : Type*} [DecidableEq V₀] {n₀ : Side} {G₀ : Gauge}
    {p₀ : BudgetPoint} {o₀ : V₀ → Site n₀} {R₀ : Census V₀} (_ : Lamps T₀ I₀ G₀ p₀ o₀ R₀) := I₀


variable {J₁ J₀ E Near Other : Type} [Countable E] {height : ℕ} {radius τ b' b'' : ℝ}
  {D : Terrain E R} {α β γ : E → Type}
  [∀ c, Fintype (α c)] [∀ c, Fintype (β c)] [∀ c, Fintype (γ c)]
  (filed : Lamps T J₁ G (X.family.path.rep N per i).p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)
  (residual : Lamps T J₀ G (X.family.path.rep N per i).p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)
  (choice : Near ⊕ Other ≃ rows (regular cash eyes A previous weights grant positive slots fits pin))
  (d : Deck ((regular cash eyes A previous weights grant positive slots fits pin).summon (fun c => choice (.inl c))) D height α)
  (d₁ : Deck filed D height β) (d₀ : Deck residual D height γ)
  (matched : ∀ c t U, Healthy (X.family.path.rep N per i).p.threshold
      (D.barrier ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) height c) U →
    d.white c t U = d₁.white c t U + d₀.white c t U)

include cash eyes W grant positive slots cap fits pos expo reg hard in
theorem purchased (simple : G.Simple) (thermal : OPE.Therm.Poetry X.family.path.levels)
    (divisions expense order : ℕ) {B ε : ℝ} (bn : 0≤B) (ep : 0<ε)
    (ready : first X simple thermal divisions expense order bn ep ≤ i) (live : i<N) (F : Tree.Forest (X.family.path.levels.clock.op i per).ratio)
    (hr : 1 ≤ radius) (width : ∀ c, (coverNumber (X.family.path.rep N per i).p.B
      (D.barrier ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) height c) : ℝ) ≤ τ)
    (modelPaid : filed.Paid weights (X.family.path.rep N per i).p.B
      ((X.family.path.rep N per i).p.supportExponent+1+1) b')
    (remainingPaid : residual.Paid weights (X.family.path.rep N per i).p.B
      ((X.family.path.rep N per i).p.supportExponent+1+1) b'')
    (afford : radius⁻¹ * (Deck.crewCost height ((X.family.path.rep N per i).p.supportExponent+1) τ *
      ((Spire.fees (X.family.path.levels.clock.op i per).ratio.count ((X.family.path.rep N per i).p.supportExponent+1+1) * b₀
        + Y^k*Γ) + b' + b'')) ≤ s) :
    let oᵢ := (X.family.path.levels.clock.op i per).ratio.parent ∘ o
    let Lout := gallery cash eyes W A previous weights grant positive slots cap fits pin
      filed residual choice d d₁ d₀ matched
    let earlier := intermediate cash eyes W A previous weights grant positive slots cap fits pin
    let charged := fun (m : R.Mode) (t : T) (U : Config G (X.family.side i per)) =>
      (Poly.toll (Stoop.radius weights radius) m : ℂ) *
        (logged Lout.K t U - logged earlier t U).part m
    ∀ (m : R.Mode) (v : V), v∈m.val → ∀ t (sensor : Config G (X.family.side i per)→ℂ),
      Measurable sensor → (∀ U, ‖sensor U‖≤B/(regulatorRun C N per i)^expense) →
      ∀ j (hj : j ≤ i), ∫ V, ‖actualTransport C (N:=N) (p:=per)
        (fun U => ((Real.sqrt (X.family.path.levels.clock.forcedAllowance i))^divisions)⁻¹ •
          (sensor U * charged m t U)) hj V‖ ∂scene X.family.path N per j ≤
        Real.exp (-((X.family.path.rep N per i).p.supportExponent+1+1) *
          (coverNumber (X.family.path.rep N per i).p.B (m.val.image oᵢ) : ℝ)) *
          (ε*(regulatorRun C N per i)^order) := by
  intro oᵢ Lout earlier charged m v occupied t sensor meas capSensor j hj
  obtain ⟨borel,localBill⟩ := WilsonPhysicalHistoryKioskInvoice.spatial cash eyes W A previous weights
    grant positive slots cap fits pin ω pos expo reg hard filed residual choice d d₁ d₀ matched
    X.makes live F hr width modelPaid remainingPaid afford
  have sameDate := (eventually_atTop.mp (WilsonPhysicalHistoryKioskHeatOrder.spatial X simple thermal
    divisions expense order bn ep)).choose_spec i ready
  exact sameDate N live.le per height (oᵢ v) (charged m t) sensor (borel m t) meas
    (fun U => (localBill m v occupied t U).1) _ (Real.exp_pos _)
    (fun U => (localBill m v occupied t U).2) capSensor j hj

end YM.Integration.WilsonPhysicalHistoryKioskMeasured
