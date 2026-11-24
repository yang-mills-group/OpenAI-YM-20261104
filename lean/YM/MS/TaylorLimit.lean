import YM.MS.CoverFlow
/-! The Taylor limits at large log heat length: iff residual jet reading and
 all-order forward/backward cost used in the tuning proof. `Budget` levels carry
 both proof of limits and comparison estimates; construct available future choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Filter Set Koszul MeasureTheory Wire Flux Real
open scoped Topology ContDiff
variable {ι A P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
   [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Scale ι}
open Domain LogTime LogTime.IntervalFamily
variable (R : LogTime.IntervalFamily ι) (y : ℝ)
variable {b : Bool} {p : Sector A} {w : Wire A E P} {m : A → ℤ}

lemma small_fact (d : ℤ) (u : R.Inst) : R.primary.length u ^ d * rate R y u=pays (fun _=>1) (d-y) u := by rw [rate, pays,one_mul, show R.primary.length u = exp (t u) from rfl, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_add]; ring_nf -- check

section
variable {L F T H : Clock ι → Row A P ℂ} {h : ℤ}
def Open (F : Clock ι → Row A P ℂ) (w : Wire A E P) (h : ℤ) (m : A→ℤ) := Bound R.dawn (fun i=> tape F w i (R.beg i)) (fun i=> pays (fun _=>1) ((fieldDim m w-h : ℤ)-y) (R.start i))

def Origin {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (F : Clock ι → Row A P ℂ) (w : Wire A X P) (j:ℕ) (i:ι) (k:X [×j]→L[ℝ] ℂ):=
    Tendsto (fun t=> iteratedFDeriv ℝ j (tape F w i t) 0) atTop (𝓝 k) -- X only Type? adjust

def weak (d : ℤ) (y:ℝ) (j : ℕ): Prop:= (d : ℝ)-y+j<0

variable {y} 
lemma int_need {j : ℕ} {k : ℤ} (hp : 0< y) (hq : y<1) : weak k y j ↔ k+j≤0:= by
   unfold weak; constructor
   · intro hx
     have h : (k:ℝ)+j<1:= by linarith
     have he : k+(j:ℤ)<1:= by exact_mod_cast h
     omega
   intro he; have h : (k:ℝ)+j≤0:= by exact_mod_cast he
   linarith

variable {R} (hv : Course b w) (hi : ∀ i, R.window i= Ici (R.beg i))
   (hf : Track b F H w) (hg : Track b L T w)
   (hl : Light R.primary (rate R y) m (lane R H) (lane R T) w h)
include hl
lemma to_price : Bound R.primary (here (tape (H-T) w)) (pays (fun _=>1) ((fieldDim m w-h:ℤ)-y)) := by
   unfold Light at hl; have ht:= hl.gain -- Light namespace missing
   exact ht.raise (Cost.of_le fun i q h=> (small_fact R y (fieldDim m w-_ ) i).le)
include hi hv hf hg
lemma origin_limit (j : ℕ) (hh : weak (fieldDim m w-h) y j) (i:ι) :
    ∃ k, Origin (F-L) w j i k :=
  needs_limit R (fun _=>zero_le_one) (along_tape R hf hg hv j) ((to_price hl).quoted _) hh hi i

omit hv hi hf hg hl in
lemma at_start (hy : 0≤ y) (u : R.Inst) : 0< rate R y u ∧ rate R y u ≤ 1 := by
   exact ⟨exp_pos _, exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hy) ((R.beg_nn _).trans u.ge))⟩

lemma orient (hy : 0≤ y) (hd : Open R y (F-L) w h m) (ho : herecost R L w h m) (hs : ∀ j : ℕ, weak (fieldDim m w-h) y j → ∀ i, Origin (F-L) w j i 0) : Light R.primary (rate R y) m (lane R F) (lane R L) w h := by
   let V:= R.comparison (fun _=> zero_le_one) hi (along_tape R hf hg hv) (fun i=> ((hf hv).1 _).sub ((hg hv).1 _) : ∀ u, ContDiff ℝ ∞ (here (tape (F-L) w) u)) (to_price hl) hd hs
   have ht : Bound R.primary (Chart (lane R (F-L)) w) (fun i=> R.primary.length i ^ (fieldDim m w-h) * rate R y i) := by
      exact V.raise (Cost.of_le fun i q h=> (small_fact R y (fieldDim m w-_) i).symm.le)
   refine ⟨?_,ho,ht⟩
   have hu : Virt R.primary (lane R (F-L)) w h m := ht.raise (Cost.of_le fun i q _=> mul_le_of_le_one_right (zpow_nonneg (R.primary.pos _).le _) (at_start hy i).2)
   unfold Virt at hu; unfold herecost Virt at ho; convert hu.add ho using 1; ext; exact (sub_add_cancel ..).symm
end
end YM.MS.Plane
