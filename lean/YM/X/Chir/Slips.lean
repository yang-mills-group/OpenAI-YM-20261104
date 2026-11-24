import YM.X.Chir.Yon
/-!
# Lens LLR. fracture implication. UV-singular channel evaluated by SBP.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Imprint
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R t c:ℝ}
local notation "S"=>Site n
local notation "D"=>Interval.mass
local notation "p"=>fund
variable (x y z:Site n)(hc:c≥0)
-- post sizes limited relative.R condition.
local notation "b"=> D x z
variable (hr:128 ≤ D x z)(hv:8 * D x y ≤ D x z)
local notation "g"=> lens b z
include hv
lemma near_layout (w:S)(h:D z w≤ b/2) : D x z≤4 * D x w ∧ D x z≤4* D y w := by
    have he:= tip x w z; have hh:=tip x y w; rw [comm w z] at he; have hz:=pay_pos x z; constructor <;> linarith only [hv,h,hz,he,hh]
local notation "Φ"=> p 3 x z
local notation "B"=> p 4 x z
local notation "A"=>p 5 x z
variable (F G: Site n→ℝ)
-- elementary gauge for envelope
variable (hp:Paying x 3 c F)(hq:Paying y 3 c G)(h₀:PreachY 4 x F c)(h₁:PreachY 4 y G c)
include h₀ h₁ hc hp hq hr
lemma spark_h (w:S)(i:Axis)(ht:g w ≠0 ∨ g (w-step i)≠0):
    D z w≤D x z/2 ∧
    ‖g (w-step i)*(F (w-step i)* G (w-step i))-g w*(F w*G w)‖ ≤ (65536*c^2)*p 7 x z:= by
      have h3:=pay_pos x z; let v:=w-step i; have h: D z w≤ b/2 ∧ D z v≤ b/2:= by
         have he:=stride z v i; unfold v at *; rw [sub_add_cancel] at he; have hh (t:Site n)(ht:g t ≠0):D z t< b/4:= lt_of_not_ge (fun hg=> ht (lens_off z t h3 hg)); rcases ht with ht|ht <;> constructor <;> linarith only [hh _ ht,he.2,he.1,hr];
      let f:=64*c*Φ; let d:=256*c*B; have hf: 0 ≤ f:=mul_nonneg (mul_nonneg (by norm_num) hc) (live _ _|>.le); have hd:0≤d:= mul_nonneg (mul_nonneg (by norm_num) hc) (live _ _|>.le)
      have h' (w:Site n) (hw:D z w≤b/2) : ‖F w‖≤ f ∧ ‖G w‖≤f:= by
           obtain ⟨hp',hq'⟩:= near_layout x y z hv w hw; have hh (t:S)(p': D x z≤4*D t w): c*p 3 t w≤f:= by unfold f; rw [mul_comm 64 c, mul_assoc]; gcongr; convert! justice (k:=3) x z t w 4 p' using 1; norm_num
           exact ⟨(hp w).trans (hh x hp'),(hq w).trans (hh y hq')⟩
      have C:‖F v-F w‖ ≤ d ∧ ‖G v-G w‖≤d:= by
           obtain ⟨ht,hw⟩:= near_layout x y z hv v h.2; have hh (P:S→ℝ)(X:S)(H:PreachY 4 X P c)(ht:b≤4*D X v): ‖P v-P w‖ ≤ d:= by
               have he:= H i v; dsimp only at he; rw [show v+step i=w from sub_add_cancel ..] at he; rw [norm_sub_rev]; apply le_trans he; unfold d; rw [mul_comm 256 c,mul_assoc]; gcongr; convert! justice (k:=4) x z X v 4 ht using 1; norm_num
           exact ⟨hh F x h₀ ht,hh G y h₁ hw⟩
      obtain ⟨u,s⟩:= C; let c':=8*b⁻¹; have hh: ‖g v - g w‖≤ c' := by convert flux_l z v h3 i using 1; unfold v; rw [sub_add_cancel]
      obtain ⟨he,hH⟩:= h' v h.2; obtain ⟨hg,hK⟩:= h' w h.1; refine ⟨h.1,?_⟩; change ‖g v*(F v*G v)-_‖ ≤ _; rw [show g v*(F v*G v)-g w*(F w*G w) =(g v-g w)*(F v*G v)+g w*((F v-F w)*G v+F w*(G v-G w)) from by ring];
      have hW:‖g w‖ ≤ 1:= by rw [Real.norm_of_nonneg (lenses z w|>.1)]; exact (lenses z w|>.2)
      refine le_trans ((norm_add_le ..).trans (add_le_add (show ‖_*(F v*G v)‖ ≤ c'*(f*f) from ?_) (show ‖g w * _‖ ≤ 1*(d*f+f*d) from ?_))) ?_; -- placeholders ambiguity
      · simp_rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr; apply (norm_add_le ..).trans; simp only [norm_mul]; gcongr
      apply le_of_eq; unfold c' f d fund; ring
-- lens norm stress.Test lengths
lemma spark_sum (i:Axis)(U:S→ℝ)(he:Paying z 3 c U) : ‖∑ w:S,(U (w+step i)-U w)* (g w*(F w*G w))‖ ≤ (65536*c^3)* p 6 x z *750 := by
     let f (w:S):=g w*(F w*G w); let Q(w:S):= U w*(f (w-step i)-f w); let v:=Finset.univ.filter (fun w:S=>g w ≠0 ∨ g (w-step i)≠0); rw [show (∑ w:S,(U (w+step i)-U w)* (g w*(F w*G w)))=∑ w∈v,Q w from ?_]; swap; · change (∑ w:S,_*f w)=_; have hz:=edge_shift U f (-step i); simp only [sub_neg_eq_add,← sub_eq_add_neg] at hz; rw [hz]; apply (sum_subset (s₁:=v) (subset_univ v) _).symm; intro k _ h; simp [v] at h; unfold f; rw [h.1,h.2,zero_mul,zero_mul,sub_zero,mul_zero]
     let C:= (65536*c^3)*p 7 x z; have hP : C≥0:= by have hz:=live (k:=7) x z; unfold C; positivity
     have hz :∑ w∈v, p 3 z w≤1500*(D x z/2):= head_pay z _ (fun i h=> (spark_h x y z hc hr hv F G hp hq h₀ h₁ i _ (mem_filter.mp h|>.2)).1 ) (by have hh:=pay_pos x z; positivity)
     calc
      _ ≤ ∑ w∈v,(p 3 z w)*C:= by
         refine (norm_sum_le ..).trans (sum_le_sum fun w hw=>?_); have h3:=spark_h x y z hc hr hv F G hp hq h₀ h₁ w i (mem_filter.mp hw|>.2); unfold Q; rw [norm_mul,show p 3 z w*C=(c*p 3 z w)*((65536*c^2)*p 7 x z) from by unfold C; ring]; exact mul_le_mul (he w) h3.2 (by positivity) (mul_nonneg hc (live _ _|>.le))
      _ ≤ (1500*(D x z/2))*C:= by rw [← Finset.sum_mul]; gcongr
      _ = _:= by unfold C fund; have ht:=pay_pos x z;field_simp; ring
end YM.PositionX.Chir.Imprint
