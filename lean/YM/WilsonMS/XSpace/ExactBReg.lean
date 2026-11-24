import YM.WilsonMS.XSpace.Swelling
import YM.WilsonMS.XSpace.Tendrils
/-!
# Exact finite-regulator position branch equality and breg consequences

Here the MS-sourced lattice matrix may be regulator singular at *every*
positive order. Do not pass source-generator vanishing estimates through
this matrix a second time. Instead equations for frames in `Substituted`
bare data share *exact* RHS, solved by the same nested (nondegenerate near
zero field-order) position scheme. This works for both point kernels and
all C1 priced smears before taking limits. The topology text:
`Front` keeps every eventual p property on every stretched large-period
schedule (and is not trivial). Honor full normalized denominator
of Bare batch used for actual perturbation. The next coupling step has still
to unfold reannouncing by XSpace χ (detector), not in this theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.FrameConj
open Function Set Filter MeasureTheory Real Finset
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget
open Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open Fiscal BMenu Rider Reservoir VisitH Sea Fray
open PowerSeries (constantCoeff coeff mk)
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n j k : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh

private def witness (T : Guard G d) : Pick G d :=
  if h : Formal T then h.actions.choose else 0

private lemma honored {T : Guard G d} (h : Formal T) : deck (witness T) = T := by
  rw [witness, dif_pos h]
  exact h.actions.choose_spec.symm
variable {A : Prescription (Ensure.deck G)} {V : Initialize G} {M : Booked (Ensure.deck G)}
  {F : MS_Data G M}
variable (μ : ℝ) (Q : Store G)
section solve
variable (hG : G.Simple) (H : Installed V F A) (hA : Rider.Commuting A)
include hA
-- useful also on Budget alternatives. High kernels summarized by the NShape
-- needed here (always at 0). Only the zero-order frame needs to be mild.
lemma exact_atPose (R : 𝕄 → Reports G d) (HV : Via (u:=Front) (Q.survey d) (fun i=> R i 0))
    (HC : TrailT (fun i=> (Q.survey d).Lays (Q.prepared d) (R i) 0) 0)
    (hZ : Fell (knot A μ d) 1)
    (Hx : NShape
      (fun i=> realm (bets A (μ-height i) (height i) d) (Program.substitute
        (Program.shift A.team (μ-height i)) (R i)) 0) (reference G d)) :
    ∀ᶠ i in Front,
      coupon (Program.shift A.team (μ-height i)) (deck ((Q.survey d).Lays (Q.prepared d) (R i)))=
        bets A (μ-height i) (height i) d * deck ((Q.survey d).Lays (Q.prepared d)
          (realm (bets A (μ-height i) (height i) d) (Program.substitute
            (Program.shift A.team (μ-height i)) (R i)))) := by
  let D := Q.survey d
  let E := Q.prepared d
  let B i := bets A (μ - height i) (height i) d
  let T i := D.Lays E (R i)
  let c (i) := Program.shift A.team (μ - height i)
  let L i := Program.substitute (c i) (R i)
  let X i := realm (B i) (L i)
  let P i := D.Lays E (L i)
  let W i := D.Lays E (X i)
  let S i := witness (coupon (c i) (deck (T i)))
  let U i := witness (B i * deck (W i))
  have hh : NShape (fun i => X i 0) (reference G d) := Hx
  have hV : Via (u := Front) D (fun i => X i 0) := (Cut_fast D hh).limit
  have hv : Via (u := Front) D (fun i => R i 0) := HV
  have hI : Via (u := Front) D (fun i => L i 0) := by
    unfold L Via
    simp_rw [pay0]
    exact hv
  have hW : ∀ᶠ i in Front, deck (U i) = B i * deck (W i) ∧ (Q.measure d).Solved (U i) (L i) := by
    filter_upwards [D.happy E (P := X) hV] with i hi
    obtain hp : Formal (B i * deck (W i)) := (Fiscal.pPrice A _ _ hA d).product hi.1
    have hc : deck (U i) = B i * deck (W i) := honored hp
    refine ⟨hc, fun n => ?_⟩
    rw [hc, ← parlance]
    exact hi.2.1 n
  have hT :
    ∀ᶠ i in Front, deck (S i) = coupon (c i) (deck (T i)) ∧ (Q.measure d).Solved (S i) (L i) := by
    filter_upwards [D.happy E (P := R) hv] with i hi
    have hC : Clean (c i) := copy_clean _ _
    have hL : deck (S i) = coupon (c i) (deck (T i)) := honored (turn_seed hi.1 hC)
    exact ⟨hL, costRoot hC _ _ _ hi.2.1 (share ..) _ hL⟩
  let g := guide G d
  have hx : Fell (fun i => stand (U i 0)) 1 := by
    have hB : Fell (fun i => constantCoeff (B i)) 1 := by
      unfold B bets
      simp_rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
      exact hZ
    have hY : Fell (fun i => constantCoeff (deck (W i))) 1 := by
      simp_rw [const_deck, ← stand0 d]
      exact Fell.stood.mp (shift_first E D hh)
    obtain h := Fell.joins hB hY
    rw [mul_one] at h
    intro p
    apply (h p).change
    filter_upwards [hW] with i hi
    rw [show stand (U i 0) = constantCoeff (deck (U i)) from (const_deck _).symm, hi.1, map_mul]
  rw [← stand0 d] at hx
  have hP : Tendsto (fun i => g (U i 0)) Front (𝓝 0) := by
    obtain hu := (Fell.stood.mpr hx).limit
    rwa [map_zero] at hu
  have hu : Tendsto (fun i => g (S i 0)) Front (𝓝 0) := by
    have hT' : TrailT (fun i => T i 0) 0 := HC
    obtain hx' := hT'.limit
    rw [map_zero] at hx'
    apply hx'.congr'
    filter_upwards [hT] with i hi
    change g (T i 0) = g (S i 0)
    have he : stand (S i 0) = stand (T i 0) := by rw [← const_deck, hi.1, turn0, const_deck]
    apply congr_arg
    apply Subtype.ext
    ext1 p
    exact Eq.symm (add_left_cancel (DFunLike.congr_fun he p : p + (S i 0).val p = p + (T i 0).val p))
  filter_upwards [hT, hW, D.unique_shift E hI hP (hW.mono fun _ hi => hi.2),
    D.unique_shift E hI hu (hT.mono fun _ hi => hi.2)] with i ht hv hi hh
  exact ht.1.symm.trans ((congr_arg deck (hh.symm.trans hi)).trans hv.1)
include hG H

theorem exact_breg (d : ℕ) :
    ∀ᶠ i in Front,
      coupon (Program.shift A.team (μ - height i)) (deck (Q.layout V i d)) =
        bets A (μ - height i) (height i) d *
          deck ((Q.survey d).Lays (Q.prepared d) (amended V μ A i d)) := by
  let R i := batch V i d
  let D := Q.survey d; let E:= Q.prepared d
  have hx : TrailT (fun i=> D.Lays E (R i) 0) 0 := by
    unfold TrailT
    rw [map_zero]; exact Fast.one (D.costsPass E V frontier)
  obtain he:= order_rates hG H μ d 0
  rw [free_match] at he
  exact exact_atPose μ Q hA R (D.gait V frontier) hx (free_lead μ hG H d) he

lemma branch_equal (d : ℕ) :
    ∀ᶠ i in Front,
      substitute (Program.shift A.team (μ - height i)) (Q.opens V i d) =
        (Q.survey d).fit (Q.prepared d) (amended V μ A i d) := by
  filter_upwards [exact_breg μ Q hG H hA d] with i hi
  rw [← Q.fits_walk, ← advertise (share ..), hi, ← parlance]
  rfl
end solve

lemma HoldT.change {g v : 𝕄 → Test n → ℂ} {p} {k : Set (Points n)} (h : HoldT k g p)
    (hp : g =ᶠ[Front] v) : HoldT k v p := by
  refine ⟨h.bill, ?_⟩
  obtain ⟨a, ha, C, hC, hV⟩ := h.pass
  exact ⟨a, ha, C, hC, (hp.and hV).mono fun i hi => hi.1 ▸ hi.2⟩

lemma NShape.changed {F G' : 𝕄 → Prediction G d} {P} (h : NShape F P) (p : F =ᶠ[Front] G') :
    NShape G' P := fun i v k hk ht =>
  HoldT.change (h _ _ _ hk ht)
    (p.mono fun i hi =>
      funext fun t => by
        dsimp only
        rw [hi])
variable (hG : G.Simple) (H : Installed V F A) (hA : Commuting A)
include hG H hA

lemma unbilled (j d : ℕ) :
    let P k := Continuum F μ k d
    NShape (fun i => substitute (Program.shift A.team (μ - height i)) (Q.opens V i d) j)
      ((Q.survey d).fit (Q.prepared d) P j) := by
  let S := Q.survey d
  let N := Q.prepared d
  obtain he := order_rates hG H μ d 0
  refine
    NShape.changed
      (fit_rate N S (free_match F μ d ▸ he) (free_match F μ d) j (F := fun i => amended V μ A i d)
        (P := fun t => Continuum F μ t d) (fun i _ => order_rates hG H μ d i))
      ((branch_equal μ Q hG H hA d).mono fun p hp => Eq.symm (congr_fun hp j))
end YM.WilsonMS.FrameConj
