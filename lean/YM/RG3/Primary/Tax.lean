import YM.RG3.Primary.Palette
import YM.Push.LOCAL_SPLITTING.Funding

/-!
# Price of canonicalizing for one literal column

Requires one extra support reserve unit at charged inputs to this
operation (hot entries only). `StemPay` at this current scale, computed at
canonical cover B include complete origin and section. Unchanged entries
elsewhere are not repriced here. Row parameter c in Radial needn't be
small. Shrink marker radii first or supply receipt at the chosen (S'). No
loss of P.derivative order across `dress`. Rewards are Lambda^*/calendar
price in pipeline, not asserted log gates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Primary
open RG Push.Local Press Forms Law Finset Function Source Lattice Wilson Marker Overlay Ac MeasureTheory
open Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V] [Fintype V] {R : Census V} (s : V) (d : Deck R P)
variable {D : ℕ} {F : Labels.Frame G D} (A : Hol G) (C : SectionData F) (w : ℝ) (θ : V → ℝ)
variable (m : ℕ → ℝ) (δ0 : ℝ)

-- Common raw price through projected sector only. Other slots supplied from
-- original `Radial.bulk`. Include `atomPrice` (and all joins actual support).
def ink (i : ℕ) := if earns s d i then atomPrice A F w * m i else 0
def gross (i : ℕ) := Real.exp ((P.p.supportExponent+1)*coverNumber P.p.B (stem s d C i)) * ink (F:=F) s d A w m i

def StemPay := (∀ i,earns s d i → P.p.supBounds (d.contents.origins s) (d.contents.support i) (d.contents.H i) (m i)) ∧
    SumBudget (fun i => θ s * gross s d A C w m i) δ0

namespace StemPay
variable {s d A C w m θ δ0}
variable (H : StemPay s d A C w θ m δ0) (hw : ∀ i,0<θ i) (hr : Readable A C P.p n w)
include H
include hr in
omit [Fintype V] in
lemma positive (i : ℕ) : 0 ≤ ink (F:=F) s d A w m i := by
  unfold ink; split
  next h => exact mul_nonneg (zero_le_one.trans (atomPrice_ge_one A _ hr.nonneg)) (H.1 _ h).1
  exact le_rfl

include hw hr
omit [Fintype V] in
lemma stock : SumBudget (ink (F:=F) s d A w m) (δ0/(θ s)) := by
  rw [div_eq_inv_mul]
  apply budget_mono (budget_scale (inv_nonneg.mpr (hw _).le) H.2) (H.positive hr) (fun i => ?_)
  rw [←mul_assoc,inv_mul_cancel₀ (hw _).ne',one_mul]
  unfold gross
  exact le_mul_of_one_le_left (H.positive hr i) (Real.one_le_exp (by positivity [P.p.exponent_pos]))

omit [Fintype V] in
lemma purchase (hd : d.Active) : (feeds s d A C hr.sound.anchored).Worth θ P.p.B (P.p.supportExponent+1) (ink (F:=F) s d A w m) δ0 := by
  refine ⟨H.positive hr,fun i U => ?_,fun x => budget_mono H.2 (fun i => ?_) (fun i => ?_)⟩
  · change ‖receipt s d A C _ _‖ ≤ _
    unfold receipt ink; split
    next hi => exact (charge_atom (d.contents.origins s) hr (hd.articles.regular i) (H.1 _ hi)).2 U
    simp
  · split
    · exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (H.positive hr _)) (Real.exp_pos _).le
    exact le_rfl
  split
  · simp only [gross,Feed.mode,feeds,Feed.locus,Poly.solo_toll]; exact le_of_eq (by ring)
  exact H.2.1 i

omit [Fintype V] in
lemma vector_total (hd : d.Active) :
    SumBudget (fun i => F.coeffSize (vector s d A i)) (δ0/(θ s)) := by
  apply budget_mono (H.stock hw hr) (fun i => Work.G08.size_nonneg F _) (fun i => ?_)
  unfold vector ink; split
  next e =>
    have ha := weighted_bound A F (d.contents.origins s) (hd.articles.regular i) hr.order hr.power (H.1 _ e)
    have hm : readPrice A F ≤ atomPrice A F w := by
      have hh : 0 ≤ w:= hr.nonneg
      have he := readPrice_pos A F
      unfold atomPrice; nlinarith
    exact ha.trans (mul_le_mul_of_nonneg_right hm (H.1 i e).1)
  simp [Labels.Frame.coeffSize]

omit [Fintype V] in
lemma combine (hd : d.Active) : Summable (vector (F:=F) s d A) ∧ F.coeffSize (comp s d A F) ≤ δ0/(θ s) := by
  have hx := H.vector_total hw hr hd
  let X (i) := vector (F:=F) s d A i
  have he : Summable fun i => ‖X i‖ := hx.2.1.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_le_size F _)
  refine ⟨he.of_norm,?_⟩
  apply le_trans _ hx.2.2
  unfold Primary.comp Labels.Frame.coeffSize
  have h (j:F.Index) : (∑' i,X i) j= ∑' i,X i j := by
    let u : F.Coeff →L[ℂ] ℂ := (LinearMap.proj (R:=ℂ) j).toContinuousLinearMap
    exact u.map_tsum he.of_norm
  have hu (j:F.Index) : Summable (fun i => ‖X i j‖) := he.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => norm_le_pi_norm (X i) j)
  let f j i := ‖X i j‖
  change _ ≤ ∑' i,∑ j,f j i
  rw [Summable.tsum_finsetSum (f:=f) (fun j _ => hu j)]
  refine sum_le_sum (fun i _ => ?_); rw [show (∑' i,vector (F:=F) s d A i)=∑' i,X i from rfl] -- rewriting nothing
  rw [h]
  exact norm_tsum_le_tsum_norm (hu i)

-- every term repriced at its actual new support/radius. Need quantitative
-- recovery externally if further steps need w raised.
omit [Fintype V] in
lemma log_bounds (hd : d.Active) {u c d' b a} (ht : d.Budget θ u c d' b a) :
    let Z := C.footprint (d.contents.origins s)
    let M := w * (δ0/(θ s))
    Article.LogBounds (dress s d A C).contents θ (u+δ0)
      (c+δ0+θ s * P.p.mass Z M) := by
  intro Z M
  let X := d.contents
  have hv := H.combine hw hr hd
  have hδ := budget_nonneg H.2
  have ho i : ‖(comp s d A F) i‖ ≤ δ0/(θ s) := (norm_le_pi_norm (comp s d A F) i).trans ((norm_le_size ..).trans hv.2)
  have hM : 0 ≤ M := mul_nonneg hr.nonneg (div_nonneg hδ (hw _).le)
  have hP : w * F.coeffSize (F.core (comp s d A F)) ≤ M := mul_le_mul_of_nonneg_left ((Work.G08.size_core ..).trans hv.2) hr.nonneg
  let B (i) := ink (F:=F) s d A w m i
  obtain ⟨c',hc,H'⟩ := ht.radial.bulk
  let q i := Nat.casesOn (motive:=fun _=>ℝ) i M (fun i => if earns s d i then B i else c' i)
  let T := (dress s d A C).contents
  refine ⟨fun i => ?_,q,fun i => ?_,fun v => ?_⟩
  · change θ i * ‖_ + _‖ ≤ _
    refine (mul_le_mul_of_nonneg_left (norm_add_le (X.units i) _) (hw i).le).trans ?_
    rw [mul_add]; apply add_le_add (ht.radial.localU _) ?_
    split
    next h => subst i; exact (mul_le_mul_of_nonneg_left (ho _) (hw s).le).trans (by rw [div_eq_inv_mul,←mul_assoc,mul_inv_cancel₀ (hw s).ne',one_mul])
    rw [norm_zero,mul_zero]; exact hδ
  · cases i with
    | zero =>
      refine ⟨hM,fun v hV => ?_⟩
      obtain rfl := mem_singleton.mp (show v∈{s} from hV)
      exact bound_weaken (presented_good _ hr _).2 hP
    | succ i =>
      change 0 ≤ (if earns s d i then B i else c' i) ∧ _
      have hq : q i.succ = if earns s d i then B i else c' i := rfl
      rw [hq]
      split_ifs with hm
      · refine ⟨H.positive hr i,fun v hh => ?_⟩
        change v∈(d.contents.rays i).val at hh
        rw [hm] at hh
        obtain rfl := mem_singleton.mp hh
        change P.p.supBounds _ (grows _ d C i) (fires _ d A C i) _
        unfold grows fires; rw [if_pos hm,if_pos hm,show B i= atomPrice A F w*m i from if_pos hm]
        exact (charge_atom _ hr (hd.articles.regular i) (H.1 _ hm)).1
      refine ⟨(hc i).1,fun v he => ?_⟩
      change P.p.supBounds _ (grows s d C i) (fires s d A C i) _
      unfold grows fires; rw [if_neg hm,if_neg hm]; exact (hc i).2 _ he
  let f (i : ℕ) := if v∈(T.rays i).val then Poly.toll θ (T.rays i)*P.p.mass (T.support i) (q i) else 0
  change SumBudget f _
  have hf : SumBudget (fun i => f (i+1)) (c+δ0) := by
    refine budget_mono (budget_plus (H' v) H.2) (fun i => ?_) (fun i => ?_)
    · unfold f; split
      · have hi : 0 ≤ q (i+1) := by unfold q; dsimp only [Nat.casesOn]; split; exact H.positive hr i; exact (hc i).1
        exact mul_nonneg (Poly.worth hw _).le (hi.trans (P.p.loMass _ _ hi))
      exact le_rfl
    change (if v∈ (X.rays i).val then _*(P.p.mass (grows s d C i) (if earns s d i then B i else c' i)) else _) ≤ (if v∈ (X.rays i).val then _ else _) + _
    split
    next hh =>
      have he : 0 ≤ Poly.toll θ (X.rays i)*P.p.mass (X.support i) (c' i) :=
        mul_nonneg (Poly.worth hw _).le ((hc i).1.trans (P.p.loMass _ _ (hc i).1))
      by_cases hu : earns s d i
      · rw [if_pos hu,grows,if_pos hu, show T.rays (i+1) = R.fire s from hu,Poly.solo_toll]
        apply le_trans _ (le_add_of_nonneg_left he)
        apply mul_le_mul_of_nonneg_left _ (hw s).le
        unfold gross B BudgetPoint.mass
        exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by gcongr; linarith)) (H.positive hr i)
      rw [if_neg hu,grows,if_neg hu]
      apply le_add_of_nonneg_right
      exact H.2.1 i
    simp only [zero_add]; exact H.2.1 i
  have hz : 0 ≤ θ s * P.p.mass Z M := mul_nonneg (hw s).le (hM.trans (P.p.loMass _ _ hM))
  have h0 : 0 ≤ f 0 ∧ f 0 ≤ θ s * P.p.mass Z M := by
    unfold f; split
    · change 0 ≤ Poly.toll θ (R.fire s)*P.p.mass Z M ∧ _
      simp only [show T.rays 0=R.fire s from rfl,Poly.solo_toll]; exact ⟨hz,le_rfl⟩
    exact ⟨le_rfl,hz⟩
  have hs := (summable_nat_add_iff 1).1 hf.2.1
  refine ⟨?_,hs,?_⟩
  · rintro (_|i); exact h0.1; exact hf.1 i
  rw [← hs.sum_add_tsum_nat_add 1, sum_range_one,add_comm]; exact add_le_add hf.2.2 h0.2
end StemPay
end YM.RG3.Primary
