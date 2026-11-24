import YM.MatchingLedger.Invoice.Country

/-!
# Arbitrary-order stalks of joint Taylor moments on the forest

Offer on **real** test local products (sym stencil or not), support and costs are not silently
taken independent of volume. Stencils really on the given horizon. For each coefficient notice
how many derivative jet losses are needed. Includes tail cost due to analytic continuation of
log monomials, does not clip the fields to compute expectations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Review
open Function Filter Set MeasureTheory Lattice RG Wilson Tree Pressure
open Push.Uniform Precision Action Top Home Cooling Gazette Periodical Kiosk Books
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)
variable {O : F.Slice G → ℝ}

def model (O : F.Slice G→ℝ)(i : ℕ) := packet (O ∘ lights F) i
lemma capModel (O : F.Slice G→ℝ)(i : ℕ): (model F O i).totalDegree≤ i:= packet_degree ..

-- meant to be reused, degree n of insertion itself distinct from vertex truncation.
structure Affords {c f:Side}{G:Gauge}{S : StepData c f}(F:Forest S.ratio)(P : Finset F.Free)(O : F.Slice G→ℝ)(n : ℕ)(M : ℝ) : Prop where
  pos : 0 ≤ M
  high (x:F.Slice G): ‖O x‖ ≤ M
  meas : Measurable O
  owns : ∀ x:Chip (Needle F G), ‖x‖ ≤ 1 → Allows (n+1) (O ∘ lights F) x M -- check Allows namespace
  pin {x y : F.Slice G}: EqOn x y P → O x=O y

def hatch (G : Gauge) (F : Forest S.ratio) (P : Finset F.Free) := P ×ˢ Finset.univ (α:=G.ColorIndex)
def height (G : Gauge)(i : ℕ) := (i * G.lieDim:ℕ)
lemma cards (G : Gauge) (P : Finset F.Free) : (hatch G F P).card=height G P.card:= by unfold hatch height; rw [Finset.card_product,Finset.card_univ,Fintype.card_fin]

-- uniform η if P.card≤given; keep P cost exposed.
namespace Affords
variable {P : Finset F.Free}{R : Support c}{n i : ℕ}{t Z M : ℝ}{A : ChartRatio G}(H : Affords F P O n M)
include H in
lemma happens : Restricted (O ∘ lights F) (hatch G F P) := by
  apply Filter.Eventually.of_forall; intro k; apply H.pin; intro j hj
  apply launch_eq (x:=k) (y:=crop _ k); intro b; rw [crop_apply,if_pos]; exact Finset.mem_product.mpr ⟨hj,Finset.mem_univ b⟩
include H in
lemma onlyHere {m : ℕ} : (model F O m).vars ⊆ hatch G F P := packet_vars (H.happens F) ((H.owns 0 (by simp)).analytic.of_le le_top)
include H in
lemma tokens (he:i≤n+1) (y:ℕ)(hy:P.card≤y): fare (model F O i)≤ M* (height G y:ℝ)^i := by
  have he' := H.owns 0 (by simp); refine (packet_cost (H.happens F) (he'.analytic.of_le le_top) M (he'.norm_le _ he)).trans ?_
  rw [cards]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by unfold height; exact_mod_cast (Nat.mul_le_mul_right _ hy)) _) H.pos

variable (hp:P ⊆ located (area F) R) (hz: 1≤Z) (ht:1≤t) (hh:t⁻¹*Z≤dial A) (hi:i≤n)
local notation "r" => (t⁻¹* Z)

-- use actual same LC cutoff. n horizon finite; no scale comparison at field definitions.
include hh hp H
lemma switches (x:F.Slice G)(hf:x∈fieldTest F R r) : O x=(O ∘ lights F) (stage F A R x):= by
  apply H.pin; intro j hj
  have hj': area F j∈R:= loc.mp (hp hj)
  unfold lights launch; rw [stage_inside F _ j hj']; exact (pedal hh (hf j hj')).2.symm

omit hh hp H

def oneWord (A : ChartRatio G)(t : ℝ)(n : ℕ) (O:F.Slice G→ℝ)(x : F.Slice G) := Periodical.run F A t (∑ i∈ Finset.range (n+1), t⁻¹^i • model F O i) x
lemma see_one (A : ChartRatio G)(t : ℝ)(n : ℕ) (x : F.Slice G) (O:F.Slice G→ℝ) : oneWord F A t n O x=∑ i∈Finset.range (n+1), t⁻¹^i * Periodical.run F A t (model F O i) x:= by unfold oneWord Periodical.run; simp

include H hp
lemma sliding (A : ChartRatio G)(t : ℝ)(x:F.Slice G) (i : ℕ): Periodical.run F A t (model F O i) x= Books.read (t • stage F A R x) (model F O i):=by
  apply read_only; intro j hj; change t*_=t*stage F A R x j; rw [onstage, if_pos (show nest F j ∈ R from (loc («a»:=area F)).mp (hp (Finset.mem_product.mp (H.onlyHere F hj)).1))]

include hi hh ht hz
lemma calculated (x:F.Slice G)(hx:x∈fieldTest F R r):
    ‖O x - oneWord F A t i O x‖ ≤ M* Z^(i+1)*(t⁻¹)^(i+1):= by
  have ht' := zero_lt_one.trans_le ht; have hh':0<t⁻¹ := inv_pos.mpr ht'; let a:= stage F A R x
  have hr: 0≤ t⁻¹*Z := by positivity
  have he : ‖a‖≤ t⁻¹*Z:= stage_range F hh hr hx
  let K:= t • a; have hK: t⁻¹ • K=a:=by simp [K, smul_smul, ht'.ne']
  have hv(p) (hq:p∈Icc 0 t⁻¹) : Allows (n+1) (O ∘ lights F) (p • K) M:= H.owns _ (compass (by rw [hK]; exact (he.trans hh).trans (min_le_left ..)) hq)
  rw [H.switches F hp hh _ hx, see_one]; simp_rw [H.sliding F hp A t x, model, packet_read]
  change ‖O _ - ∑ j∈Finset.range (i+1), t⁻¹^j * PertExtension.Series.Radial.jet _ _ K‖ ≤ _
  have H0 := annual i K hh' (fun _ he=>(hv _ he).analytic.of_le le_top) (fun _ he=> (hv _ he).norm_le (i+1) (Nat.succ_le_succ hi))
  rw [hK] at H0; refine H0.trans ?_; have hb : ‖K‖ ≤ Z := by unfold K; rw [norm_smul_of_nonneg ht'.le]; exact (mul_le_mul_of_nonneg_left he ht'.le).trans_eq (mul_inv_cancel_left₀ ht'.ne' _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb _) H.pos) (pow_nonneg hh'.le _)

omit hp hh hz

def doorway (G : Gauge) (M : ℝ)(l i:ℕ) := M + ∑ j∈ Finset.range (i+1), M * (height G l:ℝ)^j
omit ht hi in
lemma doorway_pos (l : ℕ):0≤doorway G M l i:= add_nonneg H.pos (Finset.sum_nonneg fun _ _=>mul_nonneg H.pos (by positivity))
lemma doorway_left (x : F.Slice G)(l:ℕ)(hy:P.card ≤ l) : ‖O x-oneWord F A t i O x‖≤ doorway G M l i:= by
  rw [see_one]; apply le_trans (norm_sub_le ..); refine add_le_add (H.high _) ((norm_sum_le ..).trans (Finset.sum_le_sum (fun j hj=>?_))); let u:= height G l
  have ht':0<t:= zero_lt_one.trans_le ht
  have hx:= (prime F (A:=A) j ht x (model F O j) (capModel ..)).trans (mul_le_mul_of_nonneg_right (H.tokens F (show j≤n+1 from by have h:=Finset.mem_range.mp hj; omega) l hy) (pow_nonneg ht'.le _))
  rw [norm_mul, Real.norm_of_nonneg (show 0≤(t⁻¹)^j by positivity)]; refine (mul_le_mul_of_nonneg_left hx (by positivity)).trans_eq ?_; rw [inv_pow]; field_simp
end Affords
end YM.MatchingLedger.Review
