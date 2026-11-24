import YM.SchemeRG11.Cluster.Slot
/-!
Sector bounds. No sorting required inside the integration variables.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SchemeRG11.Cluster
open Set MeasureTheory Filter Metric Function Hot MSbar
open scoped Topology ContDiff BigOperators
variable {n : ℕ}

def due (t : ℝ) := (1+t)^(4/3:ℝ)
lemma dues {t : ℝ} (h : 0<t) : due t > 0 := Real.rpow_pos_of_pos (by linarith) _
lemma cubic {t : ℝ} (h : 0<t) : due t ^ 3 = (1+t)^4 := by
  unfold due; rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith)]; norm_num
lemma raise {s t : ℝ} (h : 0<s) (hs : s≤t) : due s ≤ due t := by unfold due; gcongr
lemma dries {c : ℝ} (hc : 1≤c) : due c ≤ 4*c^2 := by
  unfold due
  refine (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤1+c) (by norm_num : (4/3:ℝ) ≤ 2)).trans ?_
  rw [Real.rpow_two]; nlinarith
lemma flakes {c : ℝ} (hc : 0<c) (ht : c≤1) : due c ≤ 4 := by simpa using (raise hc ht).trans (dries (c:=1) le_rfl)

lemma wealth {b c : ℝ} (h : 1 ≤ b) (k:b ≤ c) : due b*due b*due c ≤ (2*2*2*2:ℝ)*(b*c)^2 := by
  have hb := lt_of_lt_of_le zero_lt_one h
  have hc := lt_of_lt_of_le hb k
  apply le_of_pow_le_pow_left₀ (n:=3) (by omega) (by positivity)
  rw [mul_pow,mul_pow,cubic hb,cubic hc]
  grw [show 1+b ≤ 2*b by linarith,show 1+b ≤ 2*b by linarith,show 1+c ≤ 2*c by linarith]
  calc _ = 16^3*b^6*c^4*b^2 := by ring
       _ ≤ 16^3*b^6*c^4*c^2 := by gcongr
       _ = _ := by ring

structure Faces (p : Time) (a b c : ℝ) : Prop where
  pos : 0<a
  floor : a≤b
  ceil : b≤c
  globe : p∈tripod
  lo : b*c ≤ knot p
  up : knot p ≤ 3*b*c
  vertex i : moment p i≤c
  gated : ∃ i,moment p i=c
  pays : due a*due b*due c=due p.1*due p.2.1*due p.2.2

lemma sorted (p : Time) (hp : p∈tripod) : ∃ a b c, Faces p a b c := by
  -- rearrangements
  let a:= p.1; let b:=p.2.1; let c:=p.2.2
  have ha: 0<a:=hp.1; have hb: 0<b:=hp.2.1; have hc: 0<c:=hp.2.2
  have he(i j k:ℝ) (hi:0 < i)(hj:i≤j)(hk:j≤k)(eq:knot p=i*j+i*k+j*k)(h : ∀ s,moment p s≤k)(H:∃ l,moment p l=k)(hh:due i*due j*due k=due a*due b*due c) : ∃ a b c,Faces p a b c := by
    refine ⟨i,j,k,hi,hj,hk,hp,?_,?_,h,H,hh⟩
    · rw [eq]; nlinarith
    rw [eq]; nlinarith
  have hk : knot p=a*b+a*c+b*c:=rfl
  have suff (k : ℝ)(hA : a≤k)(hB : b≤k)(hC : c≤k) : ∀ i,moment p i≤k:= by intro i; fin_cases i; exact hA; exact hB; exact hC
  rcases le_total a b with u|u
  · rcases le_total b c with v|v
    · exact he a b c ha u v hk (by apply suff <;> linarith) ⟨2,rfl⟩ rfl
    rcases le_total a c with s|s
    · exact he a c b ha s v (by rw [hk]; ring) (by apply suff <;> linarith) ⟨1,rfl⟩ (by ring)
    exact he c a b hc s u (by rw [hk]; ring) (by apply suff <;> linarith) ⟨1,rfl⟩ (by ring)
  rcases le_total a c with v|v
  · exact he b a c hb u v (by rw [hk]; ring) (by apply suff <;> linarith) ⟨2,rfl⟩ (by ring)
  rcases le_total b c with s|s
  · exact he b c a hb s v (by rw [hk]; ring) (by apply suff <;> linarith) ⟨0,rfl⟩ (by ring)
  exact he c b a hc s u (by rw [hk]; ring) (by apply suff <;> linarith) ⟨0,rfl⟩ (by ring)

namespace Faces
variable {a b c : ℝ} {p : Time}
lemma shades (h : Faces p a b c) {d : ℝ} {x : Nodes n} (hd : 0<d) (hx : ∀ i,d ≤ bevel i x) :
    (∀ i, ‖fork p i‖ ≤ b⁻¹) ∧ (d/3)*b⁻¹ ≤ ∑ i,fork p i*bevel i x := by
  have H := Cluster.globe p h.globe
  have hb:= lt_of_lt_of_le h.pos h.floor
  have hc:=lt_of_lt_of_le hb h.ceil
  have hh i: 0<fork p i:=div_pos (lit p h.globe i) H
  constructor
  · intro i; rw [Real.norm_of_nonneg (hh i).le,fork]
    refine (div_le_div₀ hc.le (h.vertex i) (mul_pos hb hc) h.lo).trans ?_; field_simp
    exact le_rfl
  obtain ⟨i,hi⟩:=h.gated
  refine le_trans ?_ (Finset.single_le_sum (f:=fun i=> fork p i*bevel i x) (fun i _=> mul_nonneg (hh i).le (hd.le.trans (hx i))) (Finset.mem_univ i))
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hx i) (hh i).le); rw [fork,hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hc.le H h.up) hd.le); field_simp; linarith
end Faces
end YM.SchemeRG11.Cluster
