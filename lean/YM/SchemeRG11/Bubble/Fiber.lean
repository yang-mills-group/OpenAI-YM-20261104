import YM.SchemeRG11.Hot.Glow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
Orders 0 & 1 moment contractions in a two-line loop.

Each line retains an open index for the b mark. `j` denotes the number of
contracted PAIRS of internal momentum components (after shifted Gaussian moment
expansion). Densities are regulated in individual lines by (a finite linear
combination of) `[0,B]` Schwinger times. Lambda weights in those rules are
independent of dimension. No BRST or 4d quotient used here.
-/
set_option autoImplicit false
set_option maxHeartbeats 390000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Function Set MeasureTheory Metric Filter Hot MSbar
open scoped ContDiff Topology

local notation "W" => ℝ × ℝ

def braid (v : ℝ) := v*(1-v)
def halo (q : W) := q.1*braid q.2

def slab : Set ℝ := Ioc 0 1
def stem : Set W := slab ×ˢ slab
def foil (A B : ℝ) : Set W := {w | 1<w.1 ∧ w.2∈slab ∧ w.1*w.2≤A ∧ w.1*(1-w.2)≤B}
lemma stem_meas : MeasurableSet stem := measurableSet_Ioc.prod measurableSet_Ioc
lemma foil_meas (A B : ℝ) : MeasurableSet (foil A B) :=
    (measurableSet_lt (f:=fun _=>1) (g:=Prod.fst (β:=ℝ)) measurable_const measurable_fst).inter
    ((measurable_snd (t:=slab) measurableSet_Ioc).inter ((measurableSet_le (f:=fun w:W=> w.1*w.2) (g:=fun _=>A) (by fun_prop) measurable_const).inter
       (measurableSet_le (f:=fun w:W=> w.1*(1-w.2)) (g:=fun _=> B) (by fun_prop) measurable_const)))
lemma foil_span (A B : ℝ) : foil A B ⊆ Ioc 1 (A+B) ×ˢ slab := by
  rintro ⟨t,v⟩ ⟨ht,hv,ha,hb⟩; refine ⟨⟨ht,?_⟩,hv⟩; change t*v≤_ at ha; change t*(1-v)≤_ at hb; linarith
lemma fpaid (A B : ℝ) : (volume (foil A B)) < ⊤ := (measure_mono (foil_span A B)).trans_lt (by rw [show (volume:Measure W)=Measure.prod volume volume from rfl,Measure.prod_prod];simp [slab])

lemma precis {t v : ℝ} (h : v∈slab) (ht : 0<t) : halo (t,v) ∈ Icc 0 t := by
  have hh : 0<v:=h.1
  have hv : v≤1:=h.2
  refine ⟨mul_nonneg ht.le (mul_nonneg hh.le (sub_nonneg.mpr hv)),?_⟩
  exact mul_le_of_le_one_right ht.le ((mul_le_of_le_one_left (sub_nonneg.mpr hv) hv).trans (by linarith : 1-v ≤ 1))

lemma coords (A B : ℝ) (hA : 1≤A) (hB : 1≤B) (p : W) :
    p∈stem ∪ foil A B ↔ 0<p.1 ∧ p.2∈slab ∧ p.1*p.2≤A ∧ p.1*(1-p.2)≤B := by
  constructor
  · rintro (hx|⟨ht,hv,ha,hb⟩)
    · have hu : p.1∈slab:=hx.1
      have hv : p.2∈slab:=hx.2
      refine ⟨hu.1,hv,(mul_le_of_le_one_right (le_of_lt hu.1) hv.2).trans (hu.2.trans hA), (mul_le_of_le_one_right (le_of_lt hu.1) ?_).trans (hu.2.trans hB)⟩
      exact sub_le_self 1 (le_of_lt hv.1)
    exact ⟨lt_trans zero_lt_one ht,hv,ha,hb⟩
  rintro ⟨ht,hv,ha,hb⟩
  rcases lt_or_ge 1 p.1 with h|h
  · exact Or.inr ⟨h,hv,ha,hb⟩
  exact Or.inl ⟨⟨ht,h⟩,hv⟩

structure Ticket (P : ℝ→ℂ) (D : ℂ) (B C : ℝ) : Prop where
  body : ∀ t∈Icc 0 B, ‖P t‖ ≤ C
  star : ‖D‖ ≤ C
  ray : ∀ t∈Icc 0 1, ‖P t-P 0‖ ≤ C*t
  curve : ∀ t∈Icc 0 1, ‖P t-(P 0+t*D)‖ ≤ C*t^2

structure Glaze (P : ℂ→ℝ→ℂ) (D : ℂ→ℂ) : Prop where
  lit : ∀ e, ContinuousOn (P e) (Ici 0)
  fire : ∀ r≥(0:ℝ), Differentiable ℂ (fun e=>P e r)
  crack : Differentiable ℂ D
  bills : ∀ (R:ℝ), 1≤R → ∀ U : Set ℂ, IsCompact U → ∃ C>0, ∀ e∈U, Ticket (P e) (D e) R C

variable (w : ℝ→ℂ) {P : ℂ→ℝ→ℂ} {D : ℂ→ℂ} (j : Bool) (h : Glaze P D)

def index : Bool → ℕ
| true => 1
| false => 0

def phase (j : Bool) (z : ℂ) := z-1-(index j:ℕ)

def carrier (w : ℝ→ℂ) (j : Bool) (e : ℂ) (p : W) : ℂ := (p.1:ℂ)^(phase j e)*w p.2

def localTerms (P : ℝ→ℂ) (D : ℂ) (j : Bool) (r : ℝ) := P 0 + if j then r*D else 0

def purse (w : ℝ→ℂ) (P : ℂ→ℝ→ℂ) (D : ℂ→ℂ) (j : Bool) (e : ℂ) (p : W) := carrier w j e p * (P e (halo p)- localTerms (P e) (D e) j (halo p))

def pouch (w : ℝ→ℂ) (P : ℂ→ℝ→ℂ) (j : Bool) (e : ℂ) (p : W) := carrier w j e p * P e (halo p)

variable {w}
lemma open_car (p : W) (hp : 0<p.1) (e : ℂ) : DifferentiableAt ℂ (fun e=> carrier w j e p) e := by
  refine (((differentiableAt_id.sub_const 1).sub_const _).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hp.ne'))).mul_const _
lemma closed_car (hw : Continuous w) (p : W) (hp : 0<p.1) (e : ℂ) : ContinuousAt (carrier w j e) p := by
  exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hp))).comp (f:=Prod.fst) continuousAt_fst).mul (hw.continuousAt.comp continuousAt_snd)

include h
lemma purse_open (p : W) (hp : p∈stem) (e : ℂ) : DifferentiableAt ℂ (fun e=> purse w P D j e p) e := by
  unfold purse localTerms
  apply (open_car j _ hp.1.1 e).mul
  refine (h.fire _ (precis hp.2 hp.1.1).1 e).sub ((h.fire _ le_rfl e).add ?_)
  split
  · exact (h.crack e).const_mul _
  exact differentiableAt_const _
lemma pouch_open {A B : ℝ} (p : W) (hp : p∈foil A B) (e : ℂ) : DifferentiableAt ℂ (fun e=> pouch w P j e p) e := by
  have hx : 0<p.1 := lt_trans zero_lt_one hp.1
  exact (open_car j p hx e).mul (h.fire _ (precis hp.2.1 hx).1 e)

lemma halo_on (s : Set W) (e : ℂ) (hp : ∀ p ∈ s, 0<p.1 ∧ p.2∈slab) : ContinuousOn (fun p=> P e (halo p)) s := by
  exact (h.lit e).comp (show Continuous halo by unfold halo braid; fun_prop).continuousOn
   (fun p h=> (precis (hp p h).2 (hp p h).1).1)
lemma purse_on (hw : Continuous w) (e : ℂ) : ContinuousOn (purse w P D j e) stem := by
  have hc : ContinuousOn (carrier w j e) stem := fun p hp=> (closed_car j hw p hp.1.1 e).continuousWithinAt
  exact hc.mul ((halo_on h stem e (fun p hp=>⟨hp.1.1,hp.2⟩)).sub (show ContinuousOn _ stem by unfold localTerms; cases j <;> simp [halo,braid] <;> fun_prop))
lemma pouch_on (hw : Continuous w) (e : ℂ) (A B : ℝ) : ContinuousOn (pouch w P j e) (foil A B) := by
  have hc : ContinuousOn (carrier w j e) (foil A B) := fun p hp=> (closed_car j hw p (lt_trans zero_lt_one hp.1) e).continuousWithinAt
  exact hc.mul (halo_on h (foil A B) e (fun p hp=> ⟨lt_trans zero_lt_one hp.1,hp.2.1⟩))

end YM.SchemeRG11.Bubble
