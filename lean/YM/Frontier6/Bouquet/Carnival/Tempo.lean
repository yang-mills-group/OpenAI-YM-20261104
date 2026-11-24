import YM.Frontier6.Bouquet.Carnival.Midway

/-! Per-sector Taylor charge gain; other parameters' shrinkage kept by the
 anisotropic Elevator. Full tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (K:Final C F S){P Q:Ensemble}{d:Slot →ℕ}(i:P)(H: Patron S P Y) (p:Part d i)
def Tempo (x:ℝ) : ℝ:= match p with
 | none => 1
 | some w=> x^(i.val.track d w)* min x 1
lemma tempo_nonneg {x:ℝ}(h:0≤x): 0 ≤ Tempo i p x:= by cases p; exact zero_le_one; exact mul_nonneg (pow_nonneg h _) (le_min h zero_le_one)
lemma tempo_up {x:ℝ}(h:x≤1)(w:i.val.Horizon d): Tempo i (some w) x=x^(i.val.track d w+1):= by simp [Tempo,min_eq_left h,pow_succ]
lemma tempo_down {x:ℝ}(h:1≤x)(w:i.val.Horizon d): Tempo i (some w) x=x^(i.val.track d w):= by simp [Tempo,min_eq_right h]
def toil (n:ℕ) : ℕ:= match p with
 | none=> n
 | some w=> n + i.val.track d w +1

def behold (s r:ℝ): Full (normal i.val) →ₗ[ℂ] Full (normal i.val):= match p with | none=> Piece r | some w=> Piece r ∘ₗ leftOut s (i.val.track d w)
def supplements (s r:ℝ): Full (fiber P) →ₗ[ℂ] Full (fiber P):= match p with | none=> gizmo i r | some w=> gizmo i r ∘ₗ overBook i d s w
lemma supplement (s r:ℝ)(f:Full (fiber P)): supplements i p s r f=gizmo i r (demands i s p f):=by cases p <;>rfl
lemma strengthen (s r:ℝ): Elevator (home_sub i.property) (behold i p s r) (supplements i p s r):=by
   have hp:Elevator (home_sub (P:=P) i.property) (Piece r) (gizmo i r):= Elevator.panes (home_sub i.property) (strip (normal i.val) r) (strip _ _|>.contDiff)
   cases p; exact hp; exact Elevator.mul _ hp (Elevator.subtracts _ _ _)
-- within valuations r must meet suppress length for main because of its support; price proof for main doesn't depend on this!
lemma toll (n:ℕ)(B C:ℝ)(hB:1≤B)(hC:1≤C): ∃ D:ℝ,0≤D ∧ ∀ (s r t A:ℝ),0<s→0<r→0<t→t ≤ C*s→∀ f:Full (normal i.val), Fits (B*t) f → Charge (toil i p n) t f A → Charge n r (behold i p s r f) (D*A*Tempo i p (r/t)):=by
    let X:=normal i.val; obtain ⟨E,hE,h⟩:= piece_budget (X:=normal i.val) n; cases p with
    | none=>
      let Y':=(2*B)^n; have hp:0 ≤ Y':= pow_nonneg (mul_nonneg zero_le_two (zero_le_one.trans hB)) _; refine ⟨E*Y',mul_nonneg hE hp,fun s r t A hs hr ht hts f hf hh=>?_⟩; change Charge n r (Piece r f) (E*Y'*A*1); rw [mul_one,mul_assoc]; exact h r _ hr (mul_nonneg hp hh.nonneg) f (packet_coarse hh ht hr.le hB hf) -- toil reduces? 
    | some w=>
      let k:= i.val.track d w; obtain ⟨U,hU,hu⟩:= left_near (X:=X) k n C hC; obtain ⟨V,hV,hv⟩:= left_coarse (X:=X) k n B hB; refine ⟨E*(U+V),mul_nonneg hE (add_nonneg hU hV),fun s r t A hs hr ht hts f hf hh=>?_⟩; let p:=r/t; change Charge n r (Piece r (leftOut s k f)) _; have hp:0 ≤ p:= (div_pos hr ht).le; have hx:0≤ A:= hh.nonneg; rw [show E*(U+V)*A*Tempo i (some w) (r/t)= E*((U+V)*A*Tempo i (some w) p) by unfold p; ring]; by_cases ht': r≤t
      · rw [tempo_up i ((div_le_one ht).mpr ht')]; refine h r _ hr (mul_nonneg (mul_nonneg (add_nonneg hU hV) hx) (pow_nonneg hp _)) _ (?_); exact ((hu _ ht _ hts _ hr ht' f A hh).subset (fun _ h=> rings_inside h)).down_cost (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hV) hx) (pow_nonneg hp _))
      rw [tempo_down i ((one_le_div ht).mpr (le_of_not_ge ht'))]; have hH:Charge (n+k+1) t f A:= hh; exact h r _ hr (mul_nonneg (mul_nonneg (add_nonneg hU hV) hx) (pow_nonneg hp _)) _ ((hv _ _ _ ht hs (le_of_not_ge ht') f A hf (Estimate.lower hH (by omega))).down_cost (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hU) hx) (pow_nonneg hp _))) -- names not_ge orientation
variable (A:P→ℝ)
lemma reissue (r:ℝ) : outdoors i (update A i r)=outdoors i A:=by ext1 x; constructor <;> rintro ⟨j,hj,h⟩; rw [update_of_ne hj] at h; exact ⟨j,hj,h⟩; exact ⟨j,hj,(update_of_ne hj _ _) ▸ h⟩
lemma spread_cost (n:ℕ)(B C:ℝ)(hB:1≤B)(hC:1≤C): ∃ D:ℝ,0 ≤ D ∧ ∀ (A:P→ℝ)(f:Full (fiber P))(s r W:ℝ),0<s→0<r→0<A i→ A i≤C*s→ tsupport f ⊆ cylindrical _ _ (Metric.closedBall (0:normal i.val) (B*A i)) → Checks (fiber P) (paths P A) f (n+toil i p n) W → Checks (fiber P) (paths P (update A i r)) (supplements i p s r f) n (D*W*Tempo i p (r/A i)):=by
   obtain ⟨D,hD,h⟩:= toll i p n B C hB hC; refine ⟨D,hD,fun A f s r W hs hr ht hts hf hp=>?_⟩; rw [← pathways i A] at hp; rw [←pathways i _, Function.update_self, reissue]; exact Elevator.exports _ (strengthen i p s r) ht hr.le hf hp (outside i A) (h s r (A i) W hs hr ht hts)
end YM.Frontier6.Bouquet.Atelier
