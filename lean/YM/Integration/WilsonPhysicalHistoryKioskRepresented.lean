import YM.Integration.WilsonPhysicalHistoryKioskInvoice

/-! The two registered mergers act on the enrolled representative's own full forced gas.
Its quiet density is the only part of this calculation that needs the true physical marginal. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskSubset
open Function Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums
open QuadraticLocal QuadraticLocal.Shelter MeasureTheory WilsonPhysicalHistoryKioskGas
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {V T I J K E M O : Type} [DecidableEq V] [Fintype V] [Countable E]
  {P : Rep G n} {X : Activities G n} {o : V → Site n} {R : Census V} {H : ℕ}
  {fee final slack b b₁ b₀ a radius τ : ℝ}
  (raw : Lamps T I G P.p o R) (choice : M⊕O ≃ I)
  (middle : Hard T P.p X.forced X.K o R) (stage : Kiosk.Second P.p X P.activities fee final P.p.supportExponent slack)
  {filed : Lamps T J G P.p o R} {residual : Lamps T K G P.p o R}
  {D : Terrain E R} {α β γ : E → Type}
  [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
  (d : Deck (raw.summon (fun i => choice (.inl i))) D H α)
  (d₁ : Deck filed D H β) (d₀ : Deck residual D H γ)
  (matched : ∀ i t U, Healthy P.p.threshold (D.barrier o H i) U →
    d.white i t U = d₁.white i t U + d₀.white i t U)
  (w : V → ℝ) (pos : ∀ v, 0 < w v) (ha : 0≤a) (hr : 1≤radius)
  (width : ∀ i, (coverNumber P.p.B (D.barrier o H i) : ℝ) ≤ τ)
  (rawPaid : raw.Paid w P.p.B a b) (filedPaid : filed.Paid w P.p.B a b₁)
  (residualPaid : residual.Paid w P.p.B a b₀)
  (fits : radius⁻¹*(Deck.crewCost H (P.p.supportExponent+1) τ*(b+b₁+b₀)) ≤ slack)


include pos ha hr width rawPaid filedPaid residualPaid fits in
theorem represented (F : T → Config G n → Poly R)
    (income : middle.Paid w P.p.B (P.p.supportExponent+1) fee)
    (observed : ReadZone T P.p X middle F raw.log)
    (quiet : ∀ t U, (F t U).part R.quiet = (P.eval U : ℂ))
    (nonzero : ∀ U, P.eval U ≠ 0) :
    let out := output raw choice middle stage d d₁ d₀ matched
    let change := fun m t (U : Config G n) =>
      (Poly.toll (Stoop.radius w radius) m : ℂ)*(logged out.K t U-logged middle t U).part m
    (∀ t U, logged out.K t U-logged middle t U=(Deck.soap d d₁ d₀ matched).log t U) ∧
    (∀ m t, Measurable (change m t)) ∧
      ∀ (m : R.Mode) (v : V), v∈m.val → ∀ t U,
        (Healthy P.p.threshold (Animals.neighbors (H+H) (o v)) U → change m t U=0) ∧
        ‖change m t U‖*(Animals.ballCost H:ℝ) ≤ Real.exp (-a*(coverNumber P.p.B (m.val.image o):ℝ)) := by
  intro out change
  let near := raw.summon (fun c=>choice (.inl c))
  let shift := Deck.soap d d₁ d₀ matched
  have nearPaid : near.Paid w P.p.B a b :=
    raw.summonPaid w _ (choice.injective.comp Sum.inl_injective) rawPaid
  obtain ⟨_,funded,moved,density⟩:=restored raw choice middle stage d d₁ d₀ matched w pos ha hr
    width rawPaid filedPaid residualPaid fits F income observed quiet nonzero
  have after : ReadZone T P.p P.activities out.K F out.E.log := by
    intro t U
    exact ⟨Hard.packet_summing _ funded P.p.exponent_pos.le
      (fun v=>div_pos (pos v) (zero_lt_one.trans_le hr)) t U,
      (Real.exp (P.exponent U):ℂ), congrFun (density t) U⟩
  have registered (t : T) (U : Config G n) : logged out.K t U-logged middle t U=shift.log t U := by
    have nz : (F t U).part R.quiet≠0 := by rw [quiet]; exact_mod_cast nonzero U
    have old := WilsonPhysicalHistoryKioskGas.physical middle raw observed t U nz
    have next := WilsonPhysicalHistoryKioskGas.physical out.K out.E after t U nz
    calc
      _ = (out.E.log t U+logged out.K t U) - (raw.log t U+logged middle t U) +
          (raw.log t U-out.E.log t U) := by abel
      _ = _ := by rw [←next,←old,sub_self,zero_add,moved]; abel
  have written (t : T) (U : Config G n) :
      shift.log t U = near.log t U-filed.log t U-residual.log t U := by
    rw [Deck.order (x:=t) (U:=U) w pos d d₁ d₀ matched ha nearPaid filedPaid residualPaid]
    dsimp only [shift]
    abel
  refine ⟨registered,?_,?_⟩
  · intro m t
    simp_rw [change,registered]
    exact measurable_const.mul ((Poly.part_cont m).measurable.comp (Measurable.tsum fun c=>(shift.cost t c).borel))
  intro m v occupied t U
  constructor
  · intro cold
    dsimp only [change]
    rw [registered,written,WilsonPhysicalHistoryKioskCollar.healthy d d₁ d₀ matched w pos ha
      nearPaid filedPaid residualPaid m v occupied t U cold,mul_zero]
  by_cases inhabited : Nonempty E
  · obtain ⟨c⟩:=inhabited
    have base : 0≤P.p.supportExponent+1 := by linarith [P.p.exponent_pos]
    have positive : 0≤τ := (Nat.cast_nonneg _).trans (width c)
    have paid := (WilsonPhysicalHistoryKioskIncidence.funded near filed residual pos ha
      nearPaid filedPaid residualPaid m v occupied t U hr (mul_nonneg base positive)
      (fits.trans (WilsonPhysicalHistoryKioskIncidence.limit stage))).1
    have toll : 0≤Poly.toll (Stoop.radius w radius) m :=
      (Poly.worth (fun z=>(show 0<(Stoop.radius w radius) z from div_pos (pos z) (zero_lt_one.trans_le hr))) m).le
    dsimp only [change]
    rw [registered,written,norm_mul,Complex.norm_real,Real.norm_of_nonneg toll]
    exact paid
  · haveI : IsEmpty E := not_nonempty_iff.mp inhabited
    dsimp only [change]
    rw [registered]
    simp [shift,Canopy.ShiftRows.log,Real.exp_nonneg]
end YM.Integration.WilsonPhysicalHistoryKioskSubset
end
