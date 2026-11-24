import YM.Integration.WilsonPhysicalHistoryKioskCollar
import YM.Integration.WilsonPhysicalHistoryKioskCumulant

/-! The actual complete changed hard cumulant at a held Wilson configuration
is supported on the rough neighborhood of any one of its occupied sites. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskFlag
open Function Finset Lattice Wilson RG Source Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface MeasureTheory WilsonPhysicalHistoryPictureRestore
open scoped Classical BigOperators

variable {I J V : Type} [Countable I] [Countable J] [DecidableEq V] [Fintype V]
  {G : Gauge} {C : Family G} {per i N : ℕ} {L : Side}
  {x e f r s κ w b₀ b₁ z Y Γ K : ℝ} {T : Type} {A₀ : Teller G}
  {Q : ConnectedActivityE6.Target G A₀} {horizon : ConnectedActivityE6.Target.Order G w}
variable {tube : Pressure.Tube G (C.path.levels.clock.op i per)} (cash : Cash w x κ L Q horizon z tube (C.path.rep N per (i+1)))
  {k : ℕ} (eyes : Eyes cash (C.path.rep N per i) e Γ Y K k) (W : Travel.Walk cash (C.path.rep N per i) e f r s)
  {R : Census V} {o : V → Site (C.side (i+1) per)} (A : Gallery T I o (C.path.rep N per (i+1)) R)
  (previous : Lamps T J G (C.path.rep N per (i+1)).p o R) (weights : V → ℝ)
  (grant : Seal (picture A previous) weights b₀ b₁) (positive : ∀ v, 0 < weights v)
  (slots : HasSlots (C.path.rep N per (i+1)).p (C.path.rep N per (i+1)).activities) (cap : ∀ mode : R.Mode, mode.val.card ≤ k)
  (fits : 2*(b₀+b₁) ≤ K) (pin : T) (ω : V → ℝ) (pos : ∀ v,0 < ω v)
  {a q h : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid ω (C.path.rep N per (i+1)).p.B (a+2) q) (hard : A.K.Paid ω (C.path.rep N per (i+1)).p.B a h)

open QuadraticLocal.Shelter WilsonPhysicalHistoryKioskFirst
open WilsonPhysicalHistoryKioskGas WilsonPhysicalHistoryKioskRetained

private abbrev rows {T₀ I₀ V₀ : Type*} [DecidableEq V₀] {n₀ : Side} {G₀ : Gauge}
    {p₀ : BudgetPoint} {o₀ : V₀ → Site n₀} {R₀ : Census V₀} (_ : Lamps T₀ I₀ G₀ p₀ o₀ R₀) := I₀


variable {J₁ J₀ E Near Other : Type} [Countable E] {height : ℕ} {radius τ b' b'' : ℝ}
  {D : Terrain E R} {α β γ : E → Type}
  [∀ c, Fintype (α c)] [∀ c, Fintype (β c)] [∀ c, Fintype (γ c)]
  (filed : Lamps T J₁ G (C.path.rep N per i).p ((C.path.levels.clock.op i per).ratio.parent ∘ o) R)
  (residual : Lamps T J₀ G (C.path.rep N per i).p ((C.path.levels.clock.op i per).ratio.parent ∘ o) R)
  (choice : Near ⊕ Other ≃ rows (regular cash eyes A previous weights grant positive slots fits pin))
  (d : Deck ((regular cash eyes A previous weights grant positive slots fits pin).summon (fun c => choice (.inl c))) D height α)
  (d₁ : Deck filed D height β) (d₀ : Deck residual D height γ)
  (matched : ∀ c t U, Healthy (C.path.rep N per i).p.threshold
      (D.barrier ((C.path.levels.clock.op i per).ratio.parent ∘ o) height c) U →
    d.white c t U = d₁.white c t U + d₀.white c t U)

include cash eyes W grant positive slots cap fits pos expo reg hard in
theorem original (law : C.Makes) (live : i<N) (F : Tree.Forest (C.path.levels.clock.op i per).ratio)
    (hr : 1 ≤ radius) (width : ∀ c, (coverNumber (C.path.rep N per i).p.B
      (D.barrier ((C.path.levels.clock.op i per).ratio.parent ∘ o) height c) : ℝ) ≤ τ)
    (modelPaid : filed.Paid weights (C.path.rep N per i).p.B
      ((C.path.rep N per i).p.supportExponent+1+1) b')
    (remainingPaid : residual.Paid weights (C.path.rep N per i).p.B
      ((C.path.rep N per i).p.supportExponent+1+1) b'')
    (afford : radius⁻¹ * (Deck.crewCost height ((C.path.rep N per i).p.supportExponent+1) τ *
      ((Spire.fees (C.path.levels.clock.op i per).ratio.count ((C.path.rep N per i).p.supportExponent+1+1) * b₀
        + Y^k*Γ) + b' + b'')) ≤ s) :
    let oᵢ := (C.path.levels.clock.op i per).ratio.parent ∘ o
    let Lout := gallery cash eyes W A previous weights grant positive slots cap fits pin
      filed residual choice d d₁ d₀ matched
    let earlier := intermediate cash eyes W A previous weights grant positive slots cap fits pin
    let M := Deck.soap d d₁ d₀ matched
    (∀ t U, logged Lout.K t U - logged earlier t U = M.log t U) ∧
    ∀ (s : R.Mode) (v : V), v∈s.val → ∀ t U,
      (Healthy (C.path.rep N per i).p.threshold (Animals.neighbors (height+height) (oᵢ v)) U ∨
       ∃ u∈s.val, height+height < separation (oᵢ v) (oᵢ u)) →
      (logged Lout.K t U - logged earlier t U).part s = 0 := by
  intro oᵢ Lout earlier M
  obtain ⟨raw,middle,read,quiet⟩ :=
    WilsonPhysicalHistoryKioskFirst.original cash eyes W A previous weights grant positive slots cap fits pin
      ω pos expo reg hard F
  have ht : 0 ≤ (C.path.rep N per i).p.supportExponent+1+1 := by
    linarith [(C.path.rep N per i).p.exponent_pos]
  have normal (t : T) (U : Config G (C.side i per)) :
      (source A previous t U).part R.quiet = ((C.path.rep N per i).eval U : ℂ) := by
    rw [quiet, ← (law.wilson.steps N per i live).1]
  have nz (U : Config G (C.side i per)) : (C.path.rep N per i).eval U ≠ 0 :=
    (Multi.AxisShift.chosen_positive law.wilson live.le U).ne'
  have actual := WilsonPhysicalHistoryKioskSubset.restored
    (regular cash eyes A previous weights grant positive slots fits pin) choice earlier W.second
    d d₁ d₀ matched weights positive ht hr width raw modelPaid remainingPaid afford
    (source A previous) middle read normal nz
  have hard := (WilsonPhysicalHistoryKioskCumulant.original cash eyes W A previous weights grant
    positive slots cap fits pin ω pos expo reg hard filed residual choice d d₁ d₀ matched law live
    F hr width modelPaid remainingPaid afford).1
  have reading (t : T) (U : Config G (C.side i per)) :
      logged Lout.K t U - logged earlier t U = M.log t U := by
    rw [hard t U, actual.2.2.1 t U, add_sub_cancel_left]
  refine ⟨reading,?_⟩
  intro s v hv t U condition
  rw [reading]
  let localRows := (regular cash eyes A previous weights grant positive slots fits pin).summon
    (fun h : Near => choice (.inl h))
  have near := (regular cash eyes A previous weights grant positive slots fits pin).summonPaid weights
    (fun c : Near => choice (.inl c)) (choice.injective.comp Sum.inl_injective) raw
  have restore : M.log t U = localRows.log t U - filed.log t U - residual.log t U := by
    rw [Deck.order (x:=t) (U:=U) weights positive d d₁ d₀ matched ht near modelPaid remainingPaid]
    dsimp only [M]
    abel
  rw [restore]
  rcases condition with cold | ⟨u,hu,apart⟩
  · exact WilsonPhysicalHistoryKioskCollar.healthy d d₁ d₀ matched weights positive ht
      near modelPaid remainingPaid s v hv t U cold
  · exact WilsonPhysicalHistoryKioskDifference.outside d d₁ d₀ matched weights positive ht
      near modelPaid remainingPaid s v u hv hu apart t U

end YM.Integration.WilsonPhysicalHistoryKioskFlag
end
