import YM.Integration.WilsonPhysicalHistoryKioskRepresented
import YM.Integration.WilsonPhysicalHistoryKioskMeasured

/-! Run the original two mergers on the actual enrolled representatives, which can have
different regular and forced activities from the scheduled representatives. Their measured
density, incoming temperature and coarse physical budget connect them to the fixed run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskGraduate
open Function Finset Lattice Wilson RG Source Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface MeasureTheory WilsonPhysicalHistoryPictureRestore
open scoped Classical BigOperators

open Filter IterationFour PhysicalNext.Repeat.Legato Pert.Asymptotics OPE.Therm


variable {G : Gauge} (X : Run G) (simple : G.Simple) (thermal : Poetry X.family.path.levels)
  {I J₁ J₀ V E Near Other : Type} [Countable I] [Countable E] [DecidableEq V] [Fintype V]
  {N per i : ℕ} {L : Side} {T : Type}
  {x e f r s κ w b₀ b₁ z Y Γ K : ℝ} {A₀ : Teller G} {Q : ConnectedActivityE6.Target G A₀}
  {horizon : ConnectedActivityE6.Target.Order G w}
  {tube : Pressure.Tube G (X.family.path.levels.clock.op i per)}
  {P : Rep G (X.family.side (i+1) per)} {P' : Rep G (X.family.side i per)}
  (cash : Cash w x κ L Q horizon z tube P) {k : ℕ} (eyes : Eyes cash P' e Γ Y K k)
  (W : Travel.Walk cash P' e f r s)
  {R : Census V} {o : V → Site (X.family.side (i+1) per)}
  (A : Gallery T I o P R) (weights : V → ℝ) (grant : Seal A weights b₀ b₁)
  (pos : ∀ v,0<weights v) (slots : HasSlots P.p P.activities)
  (cap : ∀ m : R.Mode,m.val.card ≤ k) (bill : 2*(b₀+b₁) ≤ K) (pin : T)

private abbrev raw := Travel.raw cash eyes A weights grant pos slots bill pin
private abbrev middle := Travel.mid cash W eyes A weights grant pos slots cap bill pin

open QuadraticLocal.Shelter WilsonPhysicalHistoryKioskGas

private abbrev rows {T₀ I₀ V₀ : Type*} [DecidableEq V₀] {n₀ : Side} {G₀ : Gauge}
    {p₀ : BudgetPoint} {o₀ : V₀ → Site n₀} {R₀ : Census V₀} (_ : Lamps T₀ I₀ G₀ p₀ o₀ R₀) := I₀

variable {height : ℕ} {radius τ b' b'' : ℝ} {D : Terrain E R} {α β γ : E → Type}
  [∀ c, Fintype (α c)] [∀ c, Fintype (β c)] [∀ c, Fintype (γ c)]
  (filed : Lamps T J₁ G P'.p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)
  (residual : Lamps T J₀ G P'.p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)
  (choice : Near⊕Other ≃ rows (raw X cash eyes A weights grant pos slots bill pin))
  (d : Deck ((raw X cash eyes A weights grant pos slots bill pin).summon (fun c=>choice (.inl c))) D height α)
  (d₁ : Deck filed D height β) (d₀ : Deck residual D height γ)
  (matchDeck : ∀ c t U,Healthy P'.p.threshold
    (D.barrier ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) height c) U →
    d.white c t U=d₁.white c t U+d₀.white c t U)

include simple thermal in
theorem measured (divisions expense order : ℕ) {C ε : ℝ} (cn : 0 ≤ C) (ep : 0<ε)
    (ready : WilsonPhysicalHistoryKioskMeasured.first X simple thermal divisions expense order cn ep ≤ i)
    (live : i<N) (forest : Tree.Forest (X.family.path.levels.clock.op i per).ratio)
    (fineView : P.eval=(X.family.path.rep N per (i+1)).eval)
    (temperature : P.beta=(X.family.path.rep N per (i+1)).beta)
    (coarseView : P'.eval=(X.family.path.rep N per i).eval)
    (point : P'.p=(X.family.path.rep N per i).p)
    (hr : 1 ≤ radius) (width : ∀ c,(coverNumber P'.p.B
      (D.barrier ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) height c):ℝ) ≤ τ)
    (filedPaid : filed.Paid weights P'.p.B (P'.p.supportExponent+1+1) b')
    (residualPaid : residual.Paid weights P'.p.B (P'.p.supportExponent+1+1) b'')
    (afford : radius⁻¹*(Deck.crewCost height (P'.p.supportExponent+1) τ*
      ((Spire.fees (X.family.path.levels.clock.op i per).ratio.count (P'.p.supportExponent+1+1)*b₀+Y^k*Γ)+b'+b'')) ≤ s) :
    let oᵢ := (X.family.path.levels.clock.op i per).ratio.parent ∘ o
    let previous := middle X cash eyes W A weights grant pos slots cap bill pin
    let out := WilsonPhysicalHistoryKioskSubset.output (raw X cash eyes A weights grant pos slots bill pin)
      choice previous W.second d d₁ d₀ matchDeck
    let change := fun m t (U : Config G (X.family.side i per)) =>
      (Poly.toll (Stoop.radius weights radius) m : ℂ)*(logged out.K t U-logged previous t U).part m
    (∀ t, (X.family.path.levels.clock.op i per).push (X.family.path.rep N per (i+1)).beta
      (A.density t)=out.density t) ∧
    ∀ (m : R.Mode) (v : V), v∈m.val → ∀ t (sensor : Config G (X.family.side i per)→ℂ),
      Measurable sensor → (∀ U, ‖sensor U‖ ≤ C/(regulatorRun X.family N per i)^expense) →
      ∀ j (hj : j ≤ i), ∫ V, ‖actualTransport X.family (N:=N) (p:=per)
        (fun U=>((Real.sqrt (X.family.path.levels.clock.forcedAllowance i))^divisions)⁻¹ •
          (sensor U*change m t U)) hj V‖ ∂scene X.family.path N per j ≤ 
        Real.exp (-(P'.p.supportExponent+1+1)*(coverNumber P'.p.B (m.val.image oᵢ):ℝ))*
          (ε*(regulatorRun X.family N per i)^order) := by
  intro oᵢ previous out change
  let raw₀ := raw X cash eyes A weights grant pos slots bill pin
  let early := fun t=>(X.family.path.levels.clock.op i per).push P.beta (A.density t)
  have quiet (t) (U) : (early t U).part R.quiet=(P'.eval U:ℂ) := by
    rw [coarseView]
    change ((X.family.path.levels.clock.op i per).push P.beta (A.density t) U).part R.quiet=_
    rw [Travel.tuneQuiet cash eyes A weights grant pos slots cap bill pin t U,
      temperature,fineView]
    exact congrArg Complex.ofReal (congrFun (X.makes.wilson.steps N per i live).1 U).symm
  have nonzero (U) : P'.eval U≠0 := by
    rw [coarseView]
    exact (Multi.AxisShift.chosen_positive X.makes.wilson live.le U).ne'
  have ht : 0 ≤ P'.p.supportExponent+1+1 := by linarith [P'.p.exponent_pos]
  obtain ⟨rawPaid,hardPaid,observed⟩:=Travel.docket cash W eyes A weights grant pos slots cap bill pin forest
  have internal := WilsonPhysicalHistoryKioskSubset.restored raw₀ choice previous W.second d d₁ d₀ matchDeck
    weights pos ht hr width rawPaid filedPaid residualPaid afford early hardPaid observed quiet nonzero
  obtain ⟨_,borel,localBill⟩:=WilsonPhysicalHistoryKioskSubset.represented raw₀ choice previous W.second
    d d₁ d₀ matchDeck weights pos ht hr width rawPaid filedPaid residualPaid afford early hardPaid observed quiet nonzero
  constructor
  · intro t; rw [←temperature];exact internal.2.2.2 t
  intro m v occupied t sensor mSensor bound j hj
  have patient := (eventually_atTop.mp (WilsonPhysicalHistoryKioskHeatOrder.spatial X simple thermal
    divisions expense order cn ep)).choose_spec i ready
  exact patient N live.le per height (oᵢ v) (change m t) sensor (borel m t) mSensor
    (fun U cold=>(localBill m v occupied t U).1 (point.symm ▸ cold)) _ (Real.exp_pos _)
    (fun U=>(localBill m v occupied t U).2) bound j hj

end YM.Integration.WilsonPhysicalHistoryKioskGraduate
end
