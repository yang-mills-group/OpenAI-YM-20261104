import YM.SchemeRG11.Steam.Vigor
/-! Extract the exact open polynomial letter from the d4 star. -/
set_option autoImplicit false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4

abbrev Bit := Eye × Axis

def atEye (q : Bit) : Tri := Pi.single q.1 (basis q.2)

def own (i : Eye) : List Bit → List Axis
| [] => []
| q::l => if i=q.1 then q.2::own i l else own i l

def brick (l : List Bit) (p : Time) (x : Tri) (w : E4) (i : Eye) := tint (own i l) (moment p i) (x i-w)
def vault (l : List Bit) (p : Time) (x : Tri) (w : E4) : ℝ := (brick l p x w 0)*(brick l p x w 1)*(brick l p x w 2)

variable (p : Time)
lemma drift {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (x v : X) (r : ℝ): HasDerivAt (fun u:ℝ=> x+u • v) v r := by
   convert! (HasDerivAt.const_add x ((hasDerivAt_id' r).smul_const v)) using 1; simp
lemma plasma (q : Bit) (l : List Bit) (x : Tri) (w : E4) (r) :
    HasDerivAt (fun r:ℝ=> vault l p (x+r • atEye q) w) (vault (q::l) p (x+r • atEye q) w) r := by
  let Y := fun r : ℝ=> x+r • atEye q
  have he u i : Y u i=x i+u • (Pi.single q.1 (basis q.2):Tri) i := rfl
  have hh i : HasDerivAt (fun r:ℝ=>brick l p (Y r) w i) (if i=q.1 then brick (q::l) p (Y r) w i else 0) r := by
     split
     next hi =>
       subst i
       simp_rw [brick,own,he,Pi.single_eq_same]
       exact HasFDerivAt.comp_hasDerivAt r (((series_calm (gauze_diff (moment p q.1)) ((own q.1 l).map basis)).differentiable (by simp) _).hasFDerivAt) ((drift (x q.1) (basis q.2) r).sub_const _)
     next hi =>
       simp_rw [brick,he,Pi.single_eq_of_ne hi, smul_zero, add_zero]
       exact hasDerivAt_const ..
  convert! ((hh 0).mul (hh 1) |>.mul (hh 2)) using 1
  obtain ⟨i,a⟩:=q
  fin_cases i <;> norm_num [Eye,Fin.ext_iff,brick,vault,own,Y]

variable (hp : p∈tripod)
include hp
lemma evenhanded (l:List Bit) (R : ℝ) : ∃ b : E4→ℝ, Integrable b volume ∧ ∀ x : Tri, ‖x‖≤R → ∀ w:E4, ‖vault l p x w‖ ≤ b w := by
  obtain ⟨A,hA,e⟩:= sheer (own 0 l) (lit p hp 0) 5 R
  obtain ⟨B,hB,h⟩:=sheer (own 1 l) (lit p hp 1) 0 R
  obtain ⟨C,hC,k⟩:=sheer (own 2 l) (lit p hp 2) 0 R
  refine ⟨fun x=>A/(1+‖x‖)^5*B*C,?_,fun x hx w=>?_⟩
  · have he:= integrable_one_add_norm (μ:=volume (α:=E4)) (by norm_num [Axis] : (Module.finrank ℝ E4:ℝ)<5)
    convert! (((he.const_mul A).mul_const B).mul_const C) using 1
    ext z; rw [Real.rpow_neg (by positivity)]; congr 2; rw [Real.rpow_ofNat, div_eq_mul_inv]
  unfold vault brick; simp only [norm_mul]
  grw [e _ w ((norm_le_pi_norm x 0).trans hx),h _ w ((norm_le_pi_norm x 1).trans hx),k _ w ((norm_le_pi_norm x 2).trans hx)]
  rw [pow_zero,div_one,div_one]

omit hp in
lemma vault_calm (l : List Bit) (x : Tri) : Continuous (vault l p x) := by
  have H i : Continuous (fun w=> brick l p x w i) := (series_calm (gauze_diff (moment p i)) ((own i l).map basis)).continuous.comp (g:=tint _ _) (f:=fun y:E4=> x i-y) (by fun_prop)
  exact ((H 0).mul (H 1)).mul (H 2)
lemma vaults (l : List Bit) (x : Tri) : Integrable (vault l p x) volume := by
  obtain ⟨b,h,H⟩:=evenhanded p hp l ‖x‖
  exact Integrable.mono' h (vault_calm _ _ x).aestronglyMeasurable (Eventually.of_forall (H x le_rfl))
lemma ruby (l : List Bit) : ∀ x, series (trio p) (l.map atEye) x = ∫ w, vault l p x w := by
  induction l with
  | nil => exact fun x=> life_four p hp x
  | cons q l ih =>
      intro x
      let U := fun t:ℝ=> x+t • (atEye q)
      have H : U 0=x:=by simp [U]
      have hg:=((series_calm (trio_diff p) (l.map atEye)).differentiable (by simp) (U 0))
      have he : HasDerivAt (fun t=> series (trio p) (l.map atEye) (U t)) ((fderiv ℝ _ (U 0)) (atEye q)) 0 := hg.hasFDerivAt.comp_hasDerivAt _ (drift ..)
      obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℝ) 1).exists_bound_of_continuousOn (f:=U) (by unfold U; fun_prop)
      obtain ⟨b,hb,h⟩:=evenhanded p hp (q::l) C
      have hu:= (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun t=> vault l p (U t)) (F':=fun t=> vault (q::l) p (U t)) (bound:=b) (closedBall_mem_nhds 0 zero_lt_one)
        (Eventually.of_forall (fun t=> (vaults p hp l _).aestronglyMeasurable)) (vaults p hp l _) (vaults p hp _ _).aestronglyMeasurable (Eventually.of_forall fun w t ht=> h _ (hC t ht) w) hb (Eventually.of_forall fun w t ht=> plasma p q l x w t)).2
      simp_rw [ih] at he
      rw [H] at he hu
      exact he.unique hu
lemma arctic (μ : ℝ) (l : List Bit) (x : Tri) :
    spin μ (l.map atEye) p 0 x= (∫ w, vault l p x w:ℝ) := by
  rw [spin_four]; exact congrArg ((↑) : ℝ→ℂ) (ruby p hp l x)
end YM.SchemeRG11.Steam
