import YM.Integration.WilsonPhysicalHistoryKioskFlag
import YM.Integration.WilsonPhysicalHistoryKioskIncidence

/-! The original second-merger allotment pays the occupied rough collar
of the complete signed change on the original Wilson family. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskInvoice
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
theorem spatial (law : C.Makes) (live : i<N) (F : Tree.Forest (C.path.levels.clock.op i per).ratio)
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
    let charged := fun (m : R.Mode) (t : T) (U : Config G (C.side i per)) =>
      (Poly.toll (Stoop.radius weights radius) m : ℂ) *
        (logged Lout.K t U - logged earlier t U).part m
    (∀ m t, Measurable (charged m t)) ∧
    ∀ (m : R.Mode) (v : V), v∈m.val → ∀ t U,
      (Healthy (C.path.rep N per i).p.threshold (Animals.neighbors (height+height) (oᵢ v)) U →
        charged m t U=0) ∧
      ‖charged m t U‖*(Animals.ballCost height:ℝ) ≤
        Real.exp (-((C.path.rep N per i).p.supportExponent+1+1) *
          (coverNumber (C.path.rep N per i).p.B (m.val.image oᵢ) : ℝ)) := by
  intro oᵢ Lout earlier charged
  let M := Deck.soap d d₁ d₀ matched
  obtain ⟨registered,flag⟩ := WilsonPhysicalHistoryKioskFlag.original cash eyes W A previous weights
    grant positive slots cap fits pin ω pos expo reg hard filed residual choice d d₁ d₀ matched
    law live F hr width modelPaid remainingPaid afford
  have written (m : R.Mode) (t : T) (U : Config G (C.side i per)) :
      charged m t U = (Poly.toll (Stoop.radius weights radius) m : ℂ)*(M.log t U).part m := by
    dsimp only [charged]
    rw [registered]
  constructor
  · intro m t
    simp_rw [funext (written m t)]
    exact measurable_const.mul ((Poly.part_cont m).measurable.comp
      (Measurable.tsum fun c => (M.cost t c).borel))
  intro m v occupied t U
  constructor
  · intro clear
    dsimp only [charged]
    rw [flag m v occupied t U (Or.inl clear),mul_zero]
  by_cases cells : Nonempty E
  · obtain ⟨c⟩ := cells
    have ht : 0≤(C.path.rep N per i).p.supportExponent+1+1 := by
      linarith [(C.path.rep N per i).p.exponent_pos]
    have base : 0≤(C.path.rep N per i).p.supportExponent+1 := by
      linarith [(C.path.rep N per i).p.exponent_pos]
    have hτ : 0≤τ := (Nat.cast_nonneg _).trans (width c)
    have total := afford.trans (WilsonPhysicalHistoryKioskIncidence.limit W.second)
    have raw := (WilsonPhysicalHistoryKioskFirst.original cash eyes W A previous weights grant positive
      slots cap fits pin ω pos expo reg hard F).1
    let localRows := (regular cash eyes A previous weights grant positive slots fits pin).summon
      (fun c => choice (.inl c))
    have localPaid := Lamps.summonPaid _ weights (fun c : Near => choice (.inl c))
      (choice.injective.comp Sum.inl_injective) raw
    have paid := (WilsonPhysicalHistoryKioskIncidence.funded localRows filed residual positive ht
      localPaid modelPaid remainingPaid m v occupied t U hr (mul_nonneg base hτ) total).1
    have same : M.log t U = localRows.log t U-filed.log t U-residual.log t U :=
      by
        rw [Deck.order (x:=t) (U:=U) weights positive d d₁ d₀ matched ht localPaid modelPaid remainingPaid]
        dsimp only [M]
        abel
    have toll : 0 ≤ Poly.toll (Stoop.radius weights radius) m :=
      (Poly.worth (fun i => (show 0<(Stoop.radius weights radius) i from
        div_pos (positive i) (zero_lt_one.trans_le hr))) m).le
    rw [written,same,norm_mul,Complex.norm_real,Real.norm_of_nonneg toll]
    exact paid
  · letI : IsEmpty E := not_nonempty_iff.mp cells
    rw [written]
    simp [Canopy.ShiftRows.log,Real.exp_nonneg]

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
    let charged := fun (m : R.Mode) (t : T) (U : Config G (C.side i per)) =>
      (Poly.toll (Stoop.radius weights radius) m : ℂ) *
        (logged Lout.K t U - logged earlier t U).part m
    (∀ m t, Measurable (charged m t)) ∧
    ∀ (m : R.Mode) (v : V), v∈m.val → ∀ t U,
      (Healthy (C.path.rep N per i).p.threshold (Animals.neighbors (height+height) (oᵢ v)) U →
        charged m t U=0) ∧
      ‖charged m t U‖*(Animals.ballCost height:ℝ) ≤ 1 := by
  obtain ⟨meas,paid⟩ := spatial cash eyes W A previous weights grant positive slots cap fits pin ω
    pos expo reg hard filed residual choice d d₁ d₀ matched law live F hr width modelPaid remainingPaid afford
  refine ⟨meas,?_⟩
  intro m v occupied t U
  have ht : 0≤(C.path.rep N per i).p.supportExponent+1+1 := by
    linarith [(C.path.rep N per i).p.exponent_pos]
  exact ⟨(paid m v occupied t U).1,(paid m v occupied t U).2.trans
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Nat.cast_nonneg _)))⟩

end YM.Integration.WilsonPhysicalHistoryKioskInvoice
