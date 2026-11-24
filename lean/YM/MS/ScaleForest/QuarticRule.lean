import YM.MS.ScaleForest.Inputs

/-!
# The actual term of order two in the exponent (filed quartic rule)

Here and below use `Gauge.ColorIndex`, sum with the real orthonormal metric,
not generators of a convenient SU(N) rep. Leave internal directions in an
arbitrary auxiliary space. The tested directions `mu` for the two remaining
legs in the example will of course lie in the four-plane. `top_pair` gives the
rank-four component with equal *internal* colors and two equally polarized externals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal
open Momentum Native Cylinder
open scoped Topology ContDiff InnerProductSpace
variable {G : Gauge} {m : ℕ}

/-- External symbols in these formulas. -/
abbrev vec (x : L m) (i : G.ColorIndex) (p : SectorP m) : Shore G m := (at_g x i, p)
abbrev isA (p : Shore G m) : Prop := ∃ i j, p.1 = at_g i j
abbrev GaugeLegs (F : Mob G) : Prop := ∀ m, Uses (setOf isA) (F m)

theorem A_order (i : G.ColorIndex) (x : L m) : rank 1 (A m G x i) := mon_leaf (at_g x i)

theorem pair_order (i : G.ColorIndex) (x y : L m) : rank 2 (quill x y i) := by
  rw [quill,chew]
  exact Rails.sum _ fun j _ => Rails.sum _ fun k _ => ((A_order j x).product (A_order k y)).smul _

theorem A_gauge (i : G.ColorIndex) (x : L m) : Uses (setOf isA) (A m G x i) := by
  intro l j hj hh
  by_cases he : l.length = 1
  · obtain ⟨p,rfl⟩ := List.length_eq_one_iff.mp he
    rw [List.mem_singleton] at hj; subst j
    apply if_neg
    exact fun h => hh ⟨_,_,h⟩
  exact A_order i x l (by rw [mod_int]; omega)

theorem quill_gauge (i : G.ColorIndex) (x y : L m) : Uses (setOf isA) (quill x y i) := by
  rw [quill,chew]
  exact Uses.sum (fun _ _ => Uses.sum (fun _ _ => Uses.smul _ (Uses.pair (A_gauge _ _) (A_gauge _ _))))

theorem top_gauge (G : Gauge) : GaugeLegs (top4 G) := fun _ => Uses.smul _
    (Uses.sum fun x _=> Uses.sum fun y _=> Uses.sum fun i _=> Uses.pair (quill_gauge i x y) (quill_gauge i x y))

theorem one_A (i u : L m) (a c : G.ColorIndex) (p : SectorP m) :
    A m G i a [vec u c p] = if u=i ∧ c=a then 1 else 0 := by
  simp [A,lip,Motif.leaf,node1,onX,at_g,vec]

/-- Keep all four placements; but here already sum both orders of two
inputs (superflavor parity is even). -/
theorem bracket_rule (i : G.ColorIndex) (x y u v : L m) (j k : G.ColorIndex) (p q : SectorP m) :
    quill x y i [vec u j p, vec v k q] =
      ((if u=x ∧ v=y then 1 else 0) - (if u=y ∧ v=x then 1 else 0)) * rune j k i := by
  rw [quill,chew]
  have ht := r_ortho k j i
  simp only [Finset.sum_apply,Pi.smul_apply, pairv (A_order _ _) (A_order _ _), one_A,
    show field parity (vec u j p) = false from rfl,cross_false,one_mul,smul_eq_mul]
  rw [sub_mul]
  simp_rw [mul_add,Finset.sum_add_distrib]
  have xy (u v : L m) (j k : G.ColorIndex) : (∑ a : G.ColorIndex, ∑ c : G.ColorIndex,
        rune a c i * ((if u=x ∧ j=a then 1 else 0) * (if v=y ∧ k=c then 1 else 0))) =
      (if u=x ∧ v=y then 1 else 0) * rune j k i := by
    by_cases hu : u=x <;> by_cases hv : v=y <;> simp [hu,hv,mul_ite]
  rw [xy, xy, ht]
  simp only [and_comm, mul_neg, sub_eq_add_neg]

/-- Only gauge legs (therefore even) used here. -/
theorem quartic_splits {F H : Rack G m} (hF : Book.rank 2 F)
    {i j k u : Shore G m} (hi : field parity i = false) (hj : field parity j=false) (hk : field parity k=false)
    (hu : field parity u=false) :
    bite m G F H [i,j,k,u] =
      F [i,j]*H [k,u]+F [i,k]*H [j,u]+F [i,u]*H [j,k]+
      F [j,k]*H [i,u]+F [j,u]*H [i,k]+F [k,u]*H [i,j] := by
  have H0(t : List (Shore G m))(h : t.length ≠ 2) : F t=0 := hF _ (by rw [mod_int]; omega)
  unfold bite
  simp_rw [scattered,scatter_cons,scatter_nil,hi,hj,hk,hu,cross_false,one_mul]
  simp only [ H0 [] (by norm_num), show ∀ (i:Shore G m), F [i]=0 from fun i=> H0 [i] (by norm_num), show ∀ (i j k:Shore G m), F [i,j,k]=0 from fun i j k=> H0 _ (by norm_num), H0 [i,j,k,u] (by norm_num),
    zero_mul, zero_add,add_zero]; abel

/-- Signed wedge from a pair of half-edges. -/
def wedge (i j x y : L m) : ℂ :=
  (if x=i ∧ y=j then 1 else 0) - (if x=j ∧ y=i then 1 else 0)

theorem pair_sum (i a c d : G.ColorIndex) (x y mu j k : L m)
    (p q r s : SectorP m) :
    bite m G (quill x y i) (quill x y i) [vec j a p, vec k a q, vec mu c r, vec mu d s] =
      4 * rune a c i * rune a d i * (wedge x y j mu * wedge x y k mu) := by
  rw [quartic_splits (pair_order i x y) rfl rfl rfl rfl]
  simp_rw [bracket_rule]
  unfold wedge; simp only [and_comm,sub_self,zero_mul]; ring

theorem wedge_price (j k mu : L m) :
    (∑ x:L m, ∑ y:L m, wedge x y j mu * wedge x y k mu) = if j=k ∧ j≠mu then 2 else 0 := by
  unfold wedge
  have he (a b c d : L m) :
      (∑ x:L m,∑ y:L m, (if a=x ∧ b=y then 1 else 0 : ℂ)*(if c=x ∧ d=y then 1 else 0 : ℂ)) = if c=a ∧ d=b then 1 else 0 := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]; simp
      intro i _ hi; simp [Ne.symm hi]
      simp
    intro i _ hi; simp [Ne.symm hi]
    simp
  let d (a b x y : L m) := (if a=x ∧ b=y then 1 else 0 : ℂ)
  have hs (a b x y : L m) : (if a=y ∧ b=x then 1 else 0 : ℂ) = d b a x y := by simp only [d, and_comm]
  change ∑ x:L m, ∑ y:L m, wedge x y j mu * wedge x y k mu = _
  have hw (x y j k : L m) : wedge x y j k = d j k x y - d k j x y := by rw [wedge,hs j k x y]
  change ∀ a b c e, (∑ x:L m,∑ y:L m, d a b x y * d c e x y) = _ at he
  simp_rw [hw,sub_mul,mul_sub,Finset.sum_sub_distrib,he]
  split_ifs <;> first| (solve | norm_num) | grind

def angle (a i j : G.ColorIndex) := ∑ u : G.ColorIndex, rune a i u * rune a j u

theorem top_pair (a c d : G.ColorIndex) (j k mu : L m) (p q r s : SectorP m) :
    top4 G m [vec j a p,vec k a q, vec mu c r, vec mu d s] =
      if j=k ∧ j≠mu then -2 * angle a c d else 0 := by
  simp only [top4,sume,Finset.sum_apply,Pi.smul_apply,pair_sum]
  have he (F : L m → L m → G.ColorIndex→ℂ) :
      (∑ x,∑ y,∑ i, F x y i) = ∑ i, ∑ x, ∑ y, F x y i := by
    simp_rw [Finset.sum_comm (s:=(Finset.univ:Finset (L m))) (t:=(Finset.univ:Finset G.ColorIndex))]
  rw [he]; simp_rw [← Finset.mul_sum, wedge_price]
  split
  · rw [angle,Finset.mul_sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]; ring
  simp

/-! Color factor (no normalization absorbed into the coupling). -/
theorem angle_eq (a c d : G.ColorIndex) : angle a c d =
    (↑(inner ℝ (G.ad (Native.baseC c) (Native.baseC a)) (G.ad (Native.baseC d) (Native.baseC a))) : ℂ) := by
  unfold angle
  rw [← baseC.sum_inner_mul_inner]
  push_cast; refine Finset.sum_congr rfl fun i _ => ?_
  rw [r_ortho a c, r_ortho a d, neg_mul_neg]
  simp only [rune, scaled_tensor, real_inner_comm (baseC i)]

theorem sums_angles (h : G.Simple) (i j : G.ColorIndex) :
    (∑ a:G.ColorIndex,angle a i j) = if i=j then (G.casimir : ℂ) else 0 := by
  let b := baseC (G:=G); let x:= b i; let y:= b j
  have he (x : G.Color) : ∑ a : G.ColorIndex, ‖G.ad x (b a)‖^2 = G.casimir * inner ℝ x x :=
    (Gauge.minusKilling_sq x b).symm.trans (Gauge.trace_adjoint h x x)
  have ht : ∑ a : G.ColorIndex, inner ℝ (G.ad x (b a)) (G.ad y (b a)) = G.casimir * inner ℝ x y := by
    have hz := he (x+y)
    simp_rw [map_add,LinearMap.add_apply,norm_add_sq_real, Finset.sum_add_distrib, ← Finset.mul_sum,he] at hz
    rw [inner_add_right, inner_add_left, inner_add_left, real_inner_comm x y] at hz
    linear_combination hz / 2
  simp_rw [angle_eq,← Complex.ofReal_sum]
  change (↑(∑ a:G.ColorIndex, inner ℝ (G.ad x (b a)) (G.ad y (b a))) : ℂ)=_; rw [ht]
  unfold x y; rw [b.inner_eq_ite]; split_ifs <;> simp

end YM.MS.ScaleForest
