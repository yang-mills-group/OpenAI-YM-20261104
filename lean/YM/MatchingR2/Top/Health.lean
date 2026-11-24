import YM.MatchingR2.Top.Grid
import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin

/-!
# Unconditioned local alignment and pricing: any root (N→N−1)

Use a *single* pivot of the coarse configuration even for very remote bonds needed e.g. for
a global Hessian inverse. Its transport may grow, here at most at polynomial cost, in the
true measure after `u,v` evaluation. All finite moments. No requirement that the V's themselves
are globally good. Nor does this invoke a deterministic `Clear` constraint in estimates.

This version counts multiplicities even on wrapped paths. As noted the actual gauge choice
at conventional axes is itself a nuisance when testing symmetry of PT predictions. There is
no claim that a Taylor expansion at fixed output pivot/cap continues to transform exactly
in other conventions (or on another pivot hull).
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingR2.Top
open RG Function Wilson Lattice MeasureTheory Filter Set Finset Tree Push.SectorMeasure Pressure
open scoped Topology BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side}
variable (S : StepData c f) (F : Forest S.ratio) (β : ℝ) (o : Site c)
variable {p : ℕ}
set_option quotPrecheck false
local notation "X" => All S F G
local notation "t₀" => Real.sqrt β
local notation "V₀" => Config G c
local notation "V₁" => Config G f
local notation "Ξ" => full S F β o G
local notation "L" => S.patch.L
local notation "R" => macroR S.patch
variable {n : Side}

def coarseLink (x : Edge (Site c)) (U : V₀) := t₀*G.chord ((turned o U) x)
def fineLink (x : Edge (Site f)) (A : F.Slice G) := t₀*G.chord (F.drape A x)
lemma coarseLink_nn (x : Edge (Site c)) (U : V₀) : 0 ≤ coarseLink β o x U := mul_nonneg (Real.sqrt_nonneg _) (G.chord_nonneg _)
lemma fineLink_nn (x : Edge (Site f)) (A : F.Slice G) : 0 ≤ fineLink S F β x A := mul_nonneg (Real.sqrt_nonneg _) (G.chord_nonneg _)
lemma coarseLink_env (x : Edge (Site c)) : Envelope (coarseLink (G:=G) β o x) := by
  have he : Continuous (fun U : V₀ => (turned o U) x) := (continuous_apply x).comp (turned_continuous (G:=G) o)
  exact envelope_cart _ (continuous_const.mul (G.continuous_chord.comp he))
lemma fineLink_env (x : Edge (Site f)) : Envelope (fineLink (G:=G) S F β x) := by
  have he : Continuous (fun A : F.Slice G => (F.drape A) x) := (continuous_apply x).comp F.continuous_drape
  exact envelope_cart _ (continuous_const.mul (G.continuous_chord.comp he))
open Planned.AtomRegular.Foliage.Cube Work.E08 Axial

/-- One explicit global coarse gauge all through the projection. Adapted from
`Planned.AtomRegular.Foliage.Cube.anchored` (which supplies the variation-plane
lemma e.g. on the cover). It is used near without health assumption with this whole
RHS in the estimate. The tie is treated separately. -/
lemma pivot_estimate (V : V₀) (b : Edge (Site c)) (hn : 2*(separation o b.1 + 1)<c.val) :
    G.chord (turned o V b) ≤ 4*(separation o b.1+1:ℝ)*
      ∑ z ∈ box (separation o b.1+1), ∑ k : PlaqAxes, G.chord (faceValue V (wrap c z + o,k)) := by
  let q := separation o b.1
  let a := b.1; let i := b.2
  let l := allAxes (1 : Lattice.Order)
  let A := traveller l (expandAt o V) 0
  let g (x : Site c) := A (lift (x-o))
  let u := box (q+1)
  have hg (x : Cover) (hx : x∈u) : g (wrap c x + o) = A x := by
    unfold g; rw [add_sub_cancel_right]; apply congrArg A; apply lift_eq_iff.mpr ⟨rfl,?_⟩
    intro i; obtain ⟨h0,h1⟩ := box_test.mp hx; specialize h0 i; specialize h1 i; unfold q at h0 h1; omega
  let x := lift (a-o)
  have hw : wrap c x+o=a := by unfold x; rw [wrap_lift,sub_add_cancel]
  have hx : x ∈ u := by
    have he (j) := (box_iff_layers ..).mp (lift_mem_box (x:=o) (y:=a) le_rfl) j
    unfold u; rw [box_iff_layers]; intro j; have h := he j; change x j ∈layers q at h
    unfold layers at *; simp only [Finset.mem_Icc] at *; omega
  have hb : x+step i ∈ u := by
    obtain ⟨hi,hj⟩ := box_test.mp (lift_mem_box (x:=o) (y:=a) le_rfl)
    change _ ∈ box (separation o a+1)
    rw [box_test]; constructor <;> intro j <;> unfold x <;> simp only [Pi.add_apply,step_apply] <;> split <;>
      have ho := hi j <;> have he := hj j <;> omega
  let t := ∑ z∈u, ∑ k:PlaqAxes,G.chord (faceValue V (wrap c z+o,k))
  have hV z k : 0 ≤ G.chord (faceValue V (wrap c z+o,k)) := G.chord_nonneg _
  have h p : 0 ≤ ∑ k:PlaqAxes,G.chord (faceValue V (wrap c p+o,k)) := sum_nonneg (fun _ _=> hV ..)
  have ht' : ∀ p∈u, ∀ f : PlaqAxes, G.chord (faceValue (expandAt o V) (p,f)) ≤ t := by
    intro p hp f; unfold faceValue; rw [travel_at]; change G.chord (faceValue V (wrap c p+o,f)) ≤ _
    exact le_trans (single_le_sum (f:=fun f=>_) (fun i _=> hV p i) (mem_univ f)) (single_le_sum (fun p _=> h p) hp)
  have hQ : slab (q+1) 0 l=u := by
    ext x; simp only [slab_iff]; exact ⟨And.left,fun hh => ⟨hh,fun j hj => False.elim (hj (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩))⟩⟩
  have he := variation_plane _ (sum_nonneg (fun p _=> h p)) ht' l ((List.nodup_finRange _).map (1:Lattice.Order).injective)
    x (hQ.symm ▸ hx) i (hQ.symm ▸ hb)
  have ha : (l.length:ℝ)=4 := by simp [l,allAxes]
  calc
    _ = G.chord (expandAt o (Lattice.gauge g V) (x,i)) := by simp [expandAt,hw]; rfl
    _ = G.chord (Lattice.gauge A (expandAt o V) (x,i)) := by rw [expandAt_gauge]; simp only [Lattice.gauge,hg x hx,hg _ hb]
    _ ≤ _ := he.trans_eq (by rw [ha]; push_cast; rfl)

/-- cost exponents uniform in all weight horizons. Constants in the theorem
*not* pre-L. Torus sizes BELOW never enter them. -/
def season (n : ℕ) : ℝ := n+1
def distance (a b : Site c) := season (separation a b)
lemma season_nn (a b : Site c) : 1 ≤ distance a b := by unfold distance season; linarith [Nat.cast_nonneg (α:=ℝ) (separation a b)]
lemma wet (a b : Site c) : 0 ≤ distance a b := zero_le_one.trans (season_nn a b)
-- common constants for assembly.
def coarseBondTariff (G : Gauge) (p : ℕ) :=
  4+4*3^4*(Fintype.card PlaqAxes:ℝ)*rainFee S β G p
open Trace2.BareEstimate
def fineBondTariff (G : Gauge) (p : ℕ) := coarseBondTariff S β G p +
  (copCost G (L) S.kernel S.patch.J* (widthPort S.patch*(1+tax G β p)) + (1+collected S β p G))

lemma rain_nonneg (hβ : 1 ≤ β) (p : ℕ) (G' : Gauge) : 0 ≤ rainFee S β G' p := by
    unfold rainFee
    have hz : 0 ≤ cost1 G' S.kernel S.patch.J S.patch.L := cost1_pos ..
    have ht : 0 ≤ widthPort S.patch := by unfold widthPort; positivity
    have hu := tax_pos G' p hβ
    unfold collected quartile; positivity
lemma tariff_le_coarse (hβ : 1 ≤ β) (p : ℕ) (G' : Gauge) : 4 ≤ coarseBondTariff S β G' p := by
    have ht := rain_nonneg S β hβ p G'; unfold coarseBondTariff; exact le_add_of_nonneg_right (by positivity)
lemma tariff_le_fine (hβ : 1 ≤ β) (p : ℕ) (G' : Gauge) : coarseBondTariff S β G' p ≤ fineBondTariff S β G' p := by
    have hx : 0 ≤ copCost G' S.patch.L S.kernel S.patch.J := copCost_pos ..
    have ht : 0 ≤ widthPort S.patch := by unfold widthPort; positivity
    have hu := tax_pos G' p hβ
    unfold fineBondTariff collected quartile; exact le_add_of_nonneg_right (by positivity)
variable (H : S.patch.Branches S.kernel G)
variable (h4 : 4∣f.val) (hb : 1 ≤ β) (hp : 0 < p) (hl : Real.sqrt β ≤ c.val)
include H h4 hb hp hl

lemma coarseBond (b : Edge (Site c)) :
    LpCharge (Ξ) p (fun x => coarseLink β o b x.1) (coarseBondTariff S β G p * distance o b.1 ^ 5) := by
  letI := full_prob S F β o H
  let d := separation o b.1
  let C := coarseBondTariff S β G p
  let V := (distance o b.1)
  let A := ((V:ℝ)^5)
  let E := box (d+1)
  let w z (x:X) := ∑ k:PlaqAxes, coarseFace S F β (wrap c z + o,k) x
  have hv: 1 ≤ V := season_nn ..
  have ht : 0 ≤ V := zero_le_one.trans hv
  have ha : 1 ≤ A := one_le_pow₀ hv
  have hC : 4 ≤ C := tariff_le_coarse S β hb p G
  have ht' (x:X) := coarseLink_nn β o b x.1
  have hV : Envelope (fun x:X => coarseLink β o b x.1) := envelope_comp (f:=coarseLink β o b) (coarseLink_env β o b) measurable_fst
  by_cases he:2*(d+1)<c.val
  · have h z (_:z ∈ E) : LpCharge (Ξ) p (w z) ((Fintype.card PlaqAxes:ℝ)*rainFee S β G p) := by
      simpa [w] using LpCharge.fsum (s:=Finset.univ) (fun k:PlaqAxes => coarseFace S F β (wrap c z + o,k))
        (fun _=> rainFee S β G p) (fun i _=> coarseFace_bill S F β o H h4 hb hp _) hp
    refine LpCharge.relax (((LpCharge.fsum w (fun _=> (Fintype.card PlaqAxes:ℝ)*rainFee S β G p) h hp).scale (4*V)).monoReal hV (Eventually.of_forall (fun i=> ?_))) ?_
    · rw [Real.norm_of_nonneg (ht' i)]
      apply (mul_le_mul_of_nonneg_left (pivot_estimate o i.1 b he) (Real.sqrt_nonneg β)).trans_eq
      unfold V distance season w
      rw [mul_left_comm t₀ (4*_)]
      simp_rw [Finset.mul_sum]; rfl
    simp only [sum_const,nsmul_eq_mul,E,Corona.box_size]; rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 4*V)]
    have hk:(d:ℝ) +1 + (d+1:ℝ)+1 ≤ 3*V:=by change _ ≤ 3*((d:ℝ)+1); change 1 ≤ (d:ℝ)+1 at hv; linarith
    have hi:= rain_nonneg S β hb p G
    push_cast
    calc
      _ ≤ 4*V*((3*V)^4*((Fintype.card PlaqAxes:ℝ)*rainFee S β G p)) := by gcongr
      _ ≤ _ := by change _ ≤ (_+_)*V^5; rw [add_mul]; apply le_add_of_nonneg_of_le (by positivity) (le_of_eq (by ring))
  have hi : (c.val:ℝ) ≤ 2*V := by
    change _ ≤ 2*((d:ℝ)+1)
    exact_mod_cast Nat.le_of_not_lt he -- pushes β implicitly?
  refine ((LpCharge.const (μ:=(Ξ)) hp (4*V)).monoReal hV (Eventually.of_forall (fun i=> ?_))).relax ?_
  · rw [Real.norm_of_nonneg (ht' i)]
    change t₀ * G.chord (turned o i.1 b) ≤ 4*V; exact (mul_le_mul (hl.trans hi) (G.chord_le_two _) (G.chord_nonneg _) (by positivity)).trans_eq (by ring)
  rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 4*V)]
  apply mul_le_mul hC _ ht (by linarith [show 4 ≤ coarseBondTariff S β G p from hC])
  exact le_trans (le_of_eq (pow_one V).symm) (pow_le_pow_right₀ hv (by norm_num))

open Precision
lemma fineBond (b : Edge (Site f)) (hM : Bid.Larger (G:=G) S) :
    LpCharge (Ξ) p (fun x => fineLink S F β b x.2.2) (fineBondTariff S β G p * distance o (S.ratio.parent b.1) ^ 5) := by
  letI := full_prob S F β o H
  let a := S.ratio.parent b.1; let e := (a,b.2)
  let hN := copCost G (L) S.kernel S.patch.J; have hz : 0 ≤ hN := copCost_pos ..
  have ht := ((coarseBond S F β o H h4 hb hp hl e).add (((basket_bill S F β o H h4 hb hp a).scale hN).add (suffices_slack S F β o H hb hp e)))
  have he : Envelope (fun x:X=> fineLink S F β b x.2.2) := envelope_comp (f:=fineLink S F β b) (fineLink_env ..) (show Measurable (fun x:X=>x.2.2) from measurable_snd.comp measurable_snd)
  refine (ht.monoReal he ?_).relax ?_
  · filter_upwards [usable_ae S F β o H] with x hx
    let U := F.drape x.2.2; let V := turned o x.1; let k := (tag S).symm x.2.1
    have hi := (Work.E02.answer G (L) S.patch.J S.kernel).choose_spec.2 c f S rfl rfl rfl
      hM.2.1 hM.2.2 F U (fun i hi=>F.on_tree x.2.2 ⟨i,hi⟩) V b k (wraps S k hx a)
    have hU : G.chord ((replica S.ratio V) b) ≤ G.chord (V e) := by
      unfold replica; split
      · rw [Gauge.chord_one]; exact G.chord_nonneg _
      rfl
    have hW : 0 ≤ wire (S.prediction U k) V e := G.chord_nonneg _
    have hv : G.chord (U b * (replica S.ratio V b)⁻¹) ≤ hN*port S a U + wire (S.prediction U k) V e := by
      unfold Bid.Cops at hi; dsimp only at hi; split at hi; exact hi.trans (add_le_add_right hW _); exact hi
    rw [Real.norm_of_nonneg (fineLink_nn S F β b _)]
    let Z:= G.chord (replica S.ratio V b)
    have hall : G.chord (U b) ≤ G.chord (V e) + (hN*port S a U+wire (S.prediction U k) V e) := by
      calc
        _ ≤ G.chord (U b*(replica S.ratio V b)⁻¹)+Z := by
          simpa [Z,mul_assoc] using G.chord_triangle (U b*(replica S.ratio V b)⁻¹) (replica S.ratio V b)
        _ ≤ _ := (add_le_add hv hU).trans_eq (add_comm ..)
    apply (mul_le_mul_of_nonneg_left hall (Real.sqrt_nonneg β)).trans
    change _ ≤ t₀*G.chord (V e) + (hN*basket S F β a x+t₀*wire _ V e)
    rw [mul_add, mul_add,mul_left_comm t₀ hN]
    apply add_le_add_right (add_le_add_left (mul_le_mul_of_nonneg_left (basket_port S F β a x) hz) _) _
  change coarseBondTariff S β G p*distance o a^5+_ ≤ (_+_)*distance o a^5
  rw [Real.norm_of_nonneg hz, add_mul]; apply add_le_add_right
  apply le_mul_of_one_le_right _ (one_le_pow₀ (season_nn ..)); unfold collected quartile
  have hu := tax_pos G p hb; have hv : 0≤widthPort S.patch:= by unfold widthPort; positivity
  change 0 ≤ hN*_+_; positivity
end YM.MatchingR2.Top
