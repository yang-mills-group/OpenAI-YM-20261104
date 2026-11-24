import YM.Frontier6.Bouquet.Carnival.Ground

/-! Absolute prices in a geometric `Rhythm`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable (K:Final C F S){P Q:Ensemble}{d:Slot →ℕ}(i:P) (M:Pod→ℝ) (p:Part d i) (R: Air (S:=S) P I L Y)(B:ℝ)(z: Swing i p R B)
variable {ε δ u:ℝ}
set_option quotPrecheck false
local notation "Φ" => landscape K i M p R B
local notation "x"=> z.here
local notation "t"=> R.lengths (z.here) i
local notation "q"=> z.radius/t
lemma live_lo {y:ℝ}(h:0<y)(he:y≤1): Tempo i p y*y^swingW i p≤y:=by
   cases p with
   | none=> change (1:ℝ)*_≤_; rw [one_mul]; exact Real.rpow_le_self_of_le_one h.le he (overhead i)
   | some w=> rw [tempo_up i he,swung,← Real.rpow_natCast,← Real.rpow_add h]; simp -- simp
lemma live_hi {y:ℝ}(h:1≤y)(he:p=none→ y≤2*B): Tempo i p y*y^swingW i p ≤ max 1 ((2*B)^swingW i (d:=d) none):=by
    cases p with
    | none=> change (1:ℝ)*_≤_; rw [one_mul]; exact (Real.rpow_le_rpow (zero_le_one.trans h) (he rfl) (zero_le_one.trans (overhead i))).trans (le_max_right ..)
    | some w=> rw [tempo_down i h,swung,← Real.rpow_natCast, ← Real.rpow_add (zero_lt_one.trans_le h), add_neg_cancel,Real.rpow_zero]; exact le_max_left ..
-- companding charges. Rythym piecewise
abbrev Zoom (i:P)(d:Slot→ℕ)(B:ℝ):ℝ:=max 1 ((2*B)^swingW i (d:=d) none)
lemma zoom_pos : 0< Zoom i d B:=zero_lt_one.trans_le (le_max_left ..)
def Rhythm (ε y:ℝ):ℝ:= if y≤1 then y^ε else y^(-ε)
lemma rhythm_up {y:ℝ}(he:y≤1) : Rhythm ε y=y^ε:=if_pos he
lemma rhythm_down {y:ℝ}(he:1≤y) : Rhythm ε y=y^(-ε):=by rcases he.eq_or_lt with hh|hh; rw [←hh]; simp [Rhythm]; exact if_neg (not_le.mpr hh)
lemma rhythm_nn {y:ℝ}(he:0≤y): 0≤Rhythm ε y:=by unfold Rhythm; split <;> apply Real.rpow_nonneg he
section
variable (he: R.Welkin M) (hd:0<δ)(hδ:2*δ≤ε)
include he hd hδ
-- up still saves 1-δ: use in moment error
lemma busy (hh:z.radius≤t): Tempo i p (q)*(Φ).freight d z δ ≤ (q)^(1-δ)* R.freight d x ε:=by
    apply (membranes K i M p R B z he hd hδ).trans; have ht:=div_pos z.pos (R.length_pos (z.here) i); change 0<q at ht
    rw [sub_eq_add_neg,Real.rpow_add ht,Real.rpow_one]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (live_lo i p ht ((div_le_one (R.length_pos ..)).2 hh)) (Real.rpow_nonneg ht.le _)) (R.freight_pos d he _ _).le
lemma moves_freight (hp:δ≤1/4): Tempo i p (q)*(Φ).freight d z δ ≤ Zoom i d B* Rhythm δ (q) * R.freight d x ε:=by
    have hx:0 < (q):= div_pos z.pos (R.length_pos ..); have ht:= R.freight_pos d he z.here ε; by_cases hh:z.radius≤R.lengths z.here i
    · apply (busy K i M p R B z he hd hδ hh).trans; have h':q ≤1:=(div_le_one (R.length_pos ..)).2 hh; rw [rhythm_up h']; exact mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_ge hx h' (by linarith only [hp])).trans (le_mul_of_one_le_left (Real.rpow_nonneg hx.le δ) (le_max_left ..))) ht.le
    have h':1 ≤ q :=(one_le_div (R.length_pos ..)).2 (le_of_not_ge hh); rw [rhythm_down h']; apply (membranes K i M p R B z he hd hδ).trans; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (live_hi i p B h' (fun hv=> (div_le_iff₀ (R.length_pos ..)).mpr (z.back hv))) (Real.rpow_nonneg hx.le _)) ht.le
lemma moves_error (hp:δ≤1/4)(hu:0<u): Tempo i p (q)*(Φ).freight d z δ*(Φ).delta z u ≤ Zoom i d B* Rhythm δ (q) * R.freight d x ε * R.delta x u:=by
    have hx:0 < (q):= div_pos z.pos (R.length_pos ..); have ht:= R.freight_pos d he z.here ε; have hv:= R.delta_pos z.here hu; by_cases hh:z.radius≤ R.lengths z.here i; swap; rw [lowering K i M p R B z (le_of_not_ge hh)]; exact mul_le_mul_of_nonneg_right (moves_freight K i M p R B z he hd hδ hp) hv.le
    have h':q ≤ 1:= (div_le_one (R.length_pos ..)).2 hh; apply (mul_le_mul (busy K i M p R B z he hd hδ hh) (lending_up K i M p R B z hu hh) ((Φ).delta_pos z hu).le (mul_nonneg (Real.rpow_nonneg hx.le _) ht.le)).trans; rw [rhythm_up h']; calc
       _ = (q)^(1-δ-1/4) * R.freight d x ε * R.delta x u:=by rw [sub_eq_add_neg (1-δ),Real.rpow_add hx]; ring
       _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_ge hx h' (by linarith only [hp])).trans (le_mul_of_one_le_left (Real.rpow_nonneg hx.le δ) (le_max_left ..))) ht.le) hv.le
end
end YM.Frontier6.Bouquet.Atelier
