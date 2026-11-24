import YM.X.Rank.Flash
/-!
Nonzero simultaneous pole coefficient at both ends of a midpoint test,
with a single choice for the central B tensor.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank.Rad
open Function Set Filter Maxwell Maxwell.Free Polynomial Analysis
open scoped Topology BigOperators Classical InnerProductSpace ComplexConjugate
variable {G : Gauge} {u v d: E4}

private def photon (u v:E4)(a:Axis):= (↑(u a):ℂ)+Complex.I*v a
lemma photon_ne (hu:u≠0) (v:E4): ∃ a, photon u v a ≠0:= by
  by_contra! hh; apply hu; ext1 i; have h:= congr_arg Complex.re (hh i); simpa [photon] using h
lemma beam_nonzero {u v:E4} (hv:v≠0) : ∀ᶠ t:ℝ in atTop,u+t • v≠0 := (clears hv u {0}).mono (by intro t ht; simpa using ht)
private lemma light (h:(beam u v).eval Complex.I=0) (hv:v≠0)(c:G.ColorIndex){a b:Axis}(hx:a≠b) :
    Shine (fun t:ℝ=> (beam u v|>.eval (t:ℂ))^3 * fare c (cell a b) (cell a b) (u+t • v))
      (-(8:ℂ) * normal * (photon u v a^2+photon u v b^2)) :=by
  let p:= C (4*(normal:ℂ))*(beam u v-C 2*(wire u v a^2+wire u v b^2))
  have he:p.eval Complex.I=-(8:ℂ)*normal*(photon u v a^2+photon u v b^2):=by
    simp only [p, eval_mul,eval_C,h,eval_sub, eval_add, eval_pow, wire, eval_X,photon]; ring
  rw [← he]; apply (Shine.poly p).respects; filter_upwards [beam_nonzero (u:=u) hv] with t ht
  let x:=u+t • v; have hN:‖x‖≠0:=norm_ne_zero_iff.mpr ht
  have hz: fare c (cell a b) (cell a b) x=bareCurl a b a b x:=by
    have hh := omega_K_eq c c a b a b (y:=0) (x:=x) ht; rw [K, sub_zero, if_pos rfl] at hh
    exact hh
  change p.eval _= (beam u v|>.eval (t:ℂ))^3 * fare c (cell a b) (cell a b) x
  unfold p; rw [hz]; simp only [eval_mul, eval_C,beam_at,eval_sub,eval_pow,wire,eval_X,eval_add]
  have hh (i : Axis): (u i:ℂ)+(t:ℂ)*(v i:ℂ)=↑(x i):= by simp [x]
  simp only [hh]
  have hy: (‖x‖^2)^3*bareCurl a b a b x=4*normal*(‖x‖^2-2*(x a^2+x b^2)) := by
    rw [bare_formula a b a b ht]; simp only [house, houseM, Matrix.of_apply,wedge,kr_eq,hx,Ne.symm hx,↓reduceIte]; field_simp; ring
  change 4 * (normal:ℂ) * ((↑(‖x‖^2):ℂ) - 2 * _) = _; exact_mod_cast hy.symm

private lemma both (c:Axis→ℂ)(h:∃ i,c i≠0): ∃ i j, i≠j ∧ (c i)^2+(c j)^2≠0 := by
  obtain ⟨i,hi⟩:=h; suffices he:∃ j k:Axis, i≠j ∧ j≠k ∧ i≠k by
     obtain ⟨j,k,hj,hk,hY⟩:=he
     by_contra! H
     apply pow_ne_zero 2 hi
     linear_combination (norm:=ring_nf) (H i j hj + H i k hY-H j k hk)/2
  fin_cases i <;> decide
private lemma photon_inv (u v : E4) (i:Axis) : photon (-u) v i=-star (photon u v i):= by simp [photon, add_comm]

/-- Central weight-four probe with a legal pole, for *both* end pairings. -/
lemma hit (hv:v≠0)(h:(beam d v).eval Complex.I=0)(c:G.ColorIndex) : ∃ (w : Flavor 0)(x y:ℂ), x ≠ 0 ∧ y≠0 ∧
    Shine (fun t:ℝ=> (beam d v|>.eval (t:ℂ))^3 * fare c w w (d+t • v)) x ∧
    Shine (fun t:ℝ=> (beam d v|>.eval (t:ℂ))^3 * fare c w w (-d+t • v)) y :=by
  obtain ⟨i,j,he,hz⟩:= both (photon d v) (photon_ne (norm_pos_iff.mp ((beam_iff.mp h).1.symm ▸ norm_pos_iff.mpr hv)) v)
  let u:=-(8:ℂ)*(normal:ℂ)
  have hk : u≠0:= mul_ne_zero (by norm_num) (by exact_mod_cast normal_pos.ne')
  let q := cell i j
  let x:= photon d v i^2+photon d v j^2
  have ht:= beam_eq (beam_iff.mp h|>.2)
  refine ⟨q,u*x,u*(photon (-d) v i^2+photon (-d) v j^2),mul_ne_zero hk hz,mul_ne_zero hk ?_, light h hv c he,?_⟩
  · simp_rw [photon_inv,neg_sq, ← star_pow,← star_add]; exact star_ne_zero.mpr hz
  have H:= light (u:=-d) (ht.symm ▸ h) hv c he; rwa [ht] at H
end YM.PositionX.Rank.Rad
