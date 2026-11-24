import YM.Integration.WilsonPositionRawEpoch

/-! Position coefficients on the original auxiliary directory in the common MS field and
coupling coordinates. Both the change of coupling and each field insertion act on its
full finite Wick integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramPoint
open Filter Set Function Finset Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Arrival MS MS.Land MS.Book.Program PowerSeries Lattice
open scoped BigOperators Classical Topology

variable {G : Gauge} (Z : WilsonPrescription G) {g : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M T dial)
    {i B n : ℕ} (P : Handoff.Directory Z i B) (d : ℕ) (μ : ℝ)

def entry (x : Fin n → Cover) (v : Tags G d n) (k : ℕ) : ℂ :=
  ∑ a ∈ tally k n, ∑ j ∈ Iic (a none), cut (Dframe.reset μ T (Z.run.step i)) j (a none) *
    ∑ t, Dframe.each t (pulseU a (Dframe.D μ T (Z.run.step i) d) v) *
      coeff j (P.point_fk n d t x)

include H in
theorem filed (x : Fin n → Cover) (s : Four ℝ) (v : Tags G d n) (k : ℕ)
    (cap : Handoff.Directory.budget G n d + k ≤ B) :
    Dframe.postedPoint μ Z.scheme T d ⟨Z.run.step i,x,s⟩ k v = entry Z (T:=T) P d μ x v k := by
  rw [Dframe.seen]
  apply sum_congr rfl
  intro a ha
  have hm : a none ≤ k := ((totaled a).mp ha) ▸ single_le_sum (f:=fun l=>a l)
    (fun _ _ => Nat.zero_le _) (mem_univ none)
  unfold Dframe.orderT
  rw [rules]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := (mem_Iic.mp hj).trans hm
  exact congrArg (_ * ·) ((H.batchFromEpochFk i B P d j n x 0
    (pulseU a (Dframe.D μ T (Z.run.step i) d) v) (by omega)).1)

include H in
theorem priced (K : Set (Points n)) (compact : IsCompact K) (sep : K ⊆ conf n)
    (v : Tags G d n) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i : ℕ in atTop, ∀ B (P : Handoff.Directory Z i B)
      (x : Fin n → Cover) (s : Four ℝ), Handoff.Directory.budget G n d + k ≤ B →
      welcome (⟨Z.run.step i,x,s⟩ : Sample n) → familiar (⟨Z.run.step i,x,s⟩ : Sample n) ∈ K →
      ‖entry Z (T:=T) P d μ x v k - Dframe.meteor μ M d (familiar ⟨Z.run.step i,x,s⟩) k v‖ ≤
        C * Speed.chip (Z.run.step i) := by
  obtain ⟨C,pos,good⟩ := (H.exactbreg μ n d k v K compact sep).1
  refine ⟨C,pos,?_⟩
  filter_upwards [H.onSchedule.eventually good] with i hi
  intro B P x s cap welcome near
  rw [← filed Z H P d μ x s v k cap]
  exact hi ⟨Z.run.step i,x,s⟩ rfl welcome near

end YM.Integration.WilsonPositionProgramPoint
end
