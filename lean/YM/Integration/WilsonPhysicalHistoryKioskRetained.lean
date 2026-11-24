import YM.Integration.WilsonPhysicalHistoryKioskSubset
import YM.Integration.WilsonPhysicalHistoryKioskRough
import YM.Integration.ActualNormalizedPush

/-! Complete conditional transfer of the selected part of the earlier
marked painter with every unselected row retained in the same program.
The signed numerical comparison uses the original marker weights. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskRetained
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

abbrev gallery : Gallery T (J₁ ⊕ J₀ ⊕ Other) ((C.path.levels.clock.op i per).ratio.parent ∘ o)
    (C.path.rep N per i) R := WilsonPhysicalHistoryKioskSubset.output (P:=C.path.rep N per i)
  (filed:=filed) (residual:=residual) (regular cash eyes A previous weights grant positive slots fits pin) choice
  (intermediate cash eyes W A previous weights grant positive slots cap fits pin) W.second d d₁ d₀ matched

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
    let μ := Spire.fees (C.path.levels.clock.op i per).ratio.count
      ((C.path.rep N per i).p.supportExponent+1+1)*b₀ + Y^k*Γ
    let oᵢ := (C.path.levels.clock.op i per).ratio.parent ∘ o
    let Lout := gallery cash eyes W A previous weights grant positive slots cap fits pin
      filed residual choice d d₁ d₀ matched
    Lout.E.Paid (Stoop.radius weights radius) (C.path.rep N per i).p.B
      ((C.path.rep N per i).p.supportExponent+1+1) (radius⁻¹*b' + (radius⁻¹*b'' + radius⁻¹*μ)) ∧
    Lout.K.Paid (Stoop.radius weights radius) (C.path.rep N per i).p.B (C.path.rep N per i).p.supportExponent r ∧
    (∀ t, (C.path.levels.clock.op i per).push (C.path.rep N per (i+1)).beta
      ((picture A previous).density t) = Lout.density t) ∧
    ∀ m : R.Mode, ∀ v u : V, v ∈ m.val → u ∈ m.val → ∀ t U,
      Poly.toll weights m * ‖((regular cash eyes A previous weights grant positive slots fits pin).log t U-Lout.E.log t U).part m‖ ≤
        Real.exp (-((C.path.rep N per i).p.supportExponent+1)*
          (separation (oᵢ v) (oᵢ u)/Push.GridApprox.Attach.leg (C.path.rep N per i).p.B : ℕ)) *
        (Deck.crewCost height ((C.path.rep N per i).p.supportExponent+1) τ*(μ+b'+b'')) := by
  obtain ⟨raw,middle,read,quiet⟩ :=
    WilsonPhysicalHistoryKioskFirst.original cash eyes W A previous weights grant positive slots cap fits pin
      ω pos expo reg hard F
  have ht : 0 ≤ (C.path.rep N per i).p.supportExponent+1+1 := by
    linarith [(C.path.rep N per i).p.exponent_pos]
  have ha : 0 ≤ (C.path.rep N per i).p.supportExponent+1 := by
    linarith [(C.path.rep N per i).p.exponent_pos]
  have normalized (t : T) (U : Config G (C.side i per)) :
      (source A previous t U).part R.quiet = ((C.path.rep N per i).eval U : ℂ) := by
    rw [quiet, ← (law.wilson.steps N per i live).1]
  have nonzero (U : Config G (C.side i per)) : (C.path.rep N per i).eval U ≠ 0 :=
    (Multi.AxisShift.chosen_positive law.wilson live.le U).ne'
  have transfer := WilsonPhysicalHistoryKioskSubset.restored (regular cash eyes A previous weights grant positive slots fits pin) choice
    (intermediate cash eyes W A previous weights grant positive slots cap fits pin) W.second
    d d₁ d₀ matched weights positive ht hr width raw modelPaid remainingPaid afford
    (source A previous) middle read normalized nonzero
  refine ⟨transfer.1,transfer.2.1,fun t => ?_,?_⟩
  · exact (WilsonAllDateHarvestFiledGallery.pushed cash eyes A previous weights grant positive slots fits
      ω pos expo reg hard t).trans (transfer.2.2.2 t)
  · intro m v u hv hu t U
    rw [transfer.2.2.1 t U,add_sub_cancel_left]
    have near := (regular cash eyes A previous weights grant positive slots fits pin).summonPaid weights (fun c : Near => choice (.inl c))
      (choice.injective.comp Sum.inl_injective) raw
    have unit := Deck.paying weights positive d d₁ d₀ matched ht ha width near modelPaid remainingPaid 1 le_rfl
    simp only [div_one,inv_one,one_mul] at unit
    exact WilsonPhysicalHistoryKioskRough.separated _ positive ha unit m v u hv hu t U

end YM.Integration.WilsonPhysicalHistoryKioskRetained
