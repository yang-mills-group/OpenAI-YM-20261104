import YM.UVExt.TransitPeriod

/-! Every real link field as finite sum of site-momentum waves and covariance of frequencies under pullback by site quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths.Covering
open Lattice Laurent Bid RG Precision Wilson Exterior Matrix Set Function Filter Bloch
open scoped Classical ContDiff Topology BigOperators
variable {G : Gauge} {n m : Side} (h : Tiles n m)
lemma cell_fold (x : Site m) (p : Site n) :
     cell p (h.quot x)=cell (wrap m ((m.val/n.val) • Lattice.lift p)) x := by
 obtain ⟨k,hk⟩ := h.paid
 have hm : m.val/n.val=k := by rw [hk]; exact Nat.mul_div_cancel_left _ n.property

 have hk' : 0 < k := by by_contra! hx; have hz := m.property; exact not_le_of_gt hz (hk.trans_le (by simp [Nat.eq_zero_of_not_pos (by omega : ¬0<k)]))
 rw [hm]; suffices h' : mon (wrap m (k • Lattice.lift p))=mon p by
    calc
      cell p (h.quot x) = cell p (h.quot (wrap m (lift x))) := congr_arg (fun z=>cell p (h.quot z)) (wrap_lift x).symm
      _ = _ := by rw [fold_wrap,cell_wrap,cell]; rw [h']
 unfold mon
 have he : Lattice.lift (wrap m (k • Lattice.lift p)) = k • lift p := lift_eq_iff.mpr ⟨rfl,fun i=> by
      rw [hk]; simp only [Pi.smul_apply,nsmul_eq_mul,Nat.cast_mul]; obtain ⟨hl,hr⟩:=lift_centers p i; exact ⟨by nlinarith [mul_lt_mul_of_pos_right hl (by exact_mod_cast hk' : 0 < (k:ℤ))],by nlinarith [mul_le_mul_of_nonneg_right hr (by positivity : 0≤ (k:ℤ))]⟩⟩
 rw [he,hk]; unfold reciprocal; ext i; simp only [Pi.smul_apply,nsmul_eq_mul,smul_eq_mul,Nat.cast_mul,Int.cast_mul,Int.cast_ofNat]; field_simp [show (n.val:ℂ) ≠ 0 from by exact_mod_cast n.property.ne',show (k : ℂ)≠0 from by exact_mod_cast hk'.ne']; push_cast; ring

lemma tone_lift (p : Site n) σ : h.clone (wave (G:=G) p σ)=wave (wrap m ((m.val/n.val) • Lattice.lift p)) σ := funext fun k=>by ext l; change (cell p (h.quot k.1)* σ k.2 l).re=_; rw [cell_fold]; rfl

lemma zero_broadcast (p : Site n) : wave (G:=G) p (fun _ _=>0)=0 := by ext v l; simp [wave]
lemma add_clone (x y : Dir G n) : h.clone (x+y) = h.clone x + h.clone y := rfl

omit h
lemma wave_rows (x : Site n) (f : Site n→ℂ) : (∑ i : Site n, cell i x * ∑ j : Site n, (cell i j)⁻¹ * f j) = (n.val:ℂ)^4 * f x := by
  simp_rw [Finset.mul_sum,←mul_assoc]; rw [Finset.sum_comm]

  have he j : ∑ i, (cell i x * (cell i j)⁻¹)*f j = (if x=j then (n.val:ℂ)^4 else 0)*f j := by rw [←Finset.sum_mul]; have hx (z : Site n) : ∀ i,cell i z=cell z i := fun _=>cell_duality ..; simp_rw [hx x,hx j]; rw [orthogonal] -- placeholders
  rw [Finset.sum_eq_single x (fun j _ hj=>by rw [he,if_neg (Ne.symm hj),zero_mul]) (by simp),he,if_pos rfl]

lemma wave_sum_rep (v : Dir G n) : ∃ A : Site n → TypeFace 1→G.ColorIndex→ℂ, ∑ p : Site n, wave p (A p)=v := by
   let s := ((n.val:ℂ)^4)⁻¹
   let A (i : Site n) (t : TypeFace 1) (k : G.ColorIndex) := s * ∑ j:Site n, (cell i j)⁻¹ * ((v (j,t) k : ℝ):ℂ)
   use A; funext p; ext l
   have hv : (fun t : G.Color=>t l) (∑ i:Site n, wave i (A i) p)=_ := map_sum (PiLp.proj (𝕜:=ℝ) (2:ENNReal) (fun _=>ℝ) l) (fun i:Site n=>wave i (A i) p) _
   rw [Finset.sum_apply]; change (fun t:G.Color=>t l) (∑ i:Site n,wave i (A i) p)=_; rw [hv]
   have hz : s*(n.val:ℂ)^4=1 := by unfold s; exact inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast n.property.ne')) -- replace
   change (∑ i:Site n,(cell i p.1 * A i p.2 l).re)=_
   change (∑ i:Site n, Complex.reCLM (cell i p.1 * A i p.2 l))= _
   rw [← map_sum]; unfold A; simp_rw [mul_left_comm _ s,←Finset.mul_sum]; let b := fun i:Site n=> ((v (i,p.2) l:ℝ):ℂ)
   change (s*∑ i,cell i p.1* ∑ j, (cell i j)⁻¹*b j).re= _
   convert congr_arg Complex.re ((congr_arg (s * ·) (wave_rows p.1 b)).trans (_)) using 1 <;> try rfl
   rw [←mul_assoc,hz,one_mul]; rfl
lemma wave_add (p : Site n) (x y : TypeFace 1→G.ColorIndex→ℂ) : wave (G:=G) p (x+y)=wave p x+wave p y := by ext1 z; apply (WithLp.equiv 2 _).injective; funext t; change (cell p z.1 * (x z.2 t + y z.2 t)).re = (cell p z.1 * _).re + (cell p z.1 * _).re; rw [mul_add,Complex.add_re]
lemma wave_scale (p : Site n) (c : ℝ) (x : TypeFace 1→G.ColorIndex→ℂ) : c • wave (G:=G) p x = wave p (fun i j=> (c:ℂ) * x i j) := by ext1 z; apply (WithLp.equiv 2 _).injective; funext t; change c * (cell p z.1 * _).re = (cell p z.1 * ((c:ℂ) * _)).re; rw [mul_left_comm]; simp
private def op (L : Tensor.T (Dir G n) ℝ 2) := ((continuousMultilinearCurryFin1 ℝ (Dir G n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap) ∘L L.curryLeft
lemma op_eval (L : Tensor.T (Dir G n) ℝ 2) (u v : Dir G n) : op L u v=L ![u,v] := by
  unfold op; rw [ContinuousLinearMap.comp_apply]; change ((continuousMultilinearCurryFin1 ℝ (Dir G n) ℝ) _) v= _; rw [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply]; apply congr_arg L; ext1 i; fin_cases i <;> simp
private lemma op_eq (v) (P : Tensor.T (Dir G n) ℝ 2) : op P v v=Tensor.diagonal P v := by rw [op_eval]; apply congr_arg P; ext1 i; fin_cases i <;> rfl
private lemma elliptic (P : Tensor.T (Dir G n) ℝ 2) (x y : Dir G n) (hp : Tensor.Sym P) : op P x y = (op P y x) := ((op_eval P x y)).trans <| (hp ![x,y] (Equiv.swap (0:Fin 2) 1)).symm.trans ((congr_arg P (funext fun i=>by fin_cases i <;> simp)).trans (op_eval ..).symm)
private lemma oppose (P Q : Tensor.T (Dir G n) ℝ 2) (a : Dir G n) (q : ℝ) (hq : q ≠ 0) (he : op P (q•a) (q•a)=op Q (q•a) (q•a)) : op P a a=op Q a a := by
  rw [map_smul,map_smul,ContinuousLinearMap.smul_apply,map_smul,map_smul,ContinuousLinearMap.smul_apply] at he
  change q * (q * op P a a) = q * (q * op Q a a) at he
  exact mul_left_cancel₀ hq (mul_left_cancel₀ hq he)
lemma wave_span {P Q : Tensor.T (Dir G n) ℝ 2} (hP : Tensor.Sym P) (hQ : Tensor.Sym Q)
    (hh : ∀ p q:Site n,∀ σ τ, (∀ k ℓ,‖σ k ℓ‖≤1) → (∀ k ℓ,‖τ k ℓ‖≤1) → Tensor.diagonal P (wave p σ +wave q τ)=Tensor.diagonal Q (wave p σ + wave q τ)) : P=Q := by
   -- first unnormalized pairs by dilation; then polarization; then sums
   have hBoth (p q : Site n) (σ τ : TypeFace 1→G.ColorIndex→ℂ) : op P (wave p σ+wave q τ) (wave p σ+wave q τ) = op Q (wave p σ+wave q τ) (wave p σ +wave q τ) := by
      let x:ℝ := (1+max ‖σ‖ ‖τ‖)⁻¹; have hp : 1≤1+max ‖σ‖ ‖τ‖ := le_add_of_nonneg_right (by positivity)
      suffices hr : op P (x • (wave p σ + wave q τ)) (x • (wave p σ + wave q τ)) = op Q (x • (wave p σ+wave q τ)) (x • (wave p σ + wave q τ)) by exact oppose _ _ _ _ (by unfold x; positivity) hr
      rw [smul_add,wave_scale,wave_scale,op_eq,op_eq]
      have hι {a : TypeFace 1 → G.ColorIndex →ℂ} (t : ‖a‖ ≤ 1+max ‖σ‖ ‖τ‖) : ∀ p k,‖(x:ℂ)*a p k‖≤1 := by
         intro r k
         rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by unfold x; positivity)]
         unfold x; exact le_trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ _).trans (norm_le_pi_norm a r) |>.trans t) (by positivity)) (ge_of_eq (Eq.symm (inv_mul_cancel₀ (by positivity))))
      exact hh p q _ _ (hι (le_trans (le_max_left _ _) (le_add_of_nonneg_left zero_le_one))) (hι ((le_max_right _ _).trans (le_add_of_nonneg_left zero_le_one)))
   have hPair (p q : Site n) (σ τ) : op P (wave p σ) (wave q τ) = op Q (wave p σ) (wave q τ) := by
      have he (i x) : op P (wave i x) (wave i x) = op Q (wave i x) (wave i x) := by
          convert hBoth i i x 0 using 1 <;> try rfl
          all_goals rw [show wave (G:=G) i 0 = 0 from zero_broadcast i, add_zero]
      have ht := hBoth p q σ τ
      rw [map_add (op P), map_add (f:=(op P _+op P _)),ContinuousLinearMap.add_apply,map_add (op Q),map_add (f:=(op Q _+op Q _)),ContinuousLinearMap.add_apply (op Q _) (op Q _) (wave p σ),ContinuousLinearMap.add_apply (op Q _) (op Q _) (wave q τ)] at ht
      simp only [ContinuousLinearMap.add_apply] at ht
      linarith [elliptic P (wave q τ) (wave p σ) hP,elliptic Q (wave q τ) (wave p σ) hQ,he p σ,he q τ]
   apply Tensor.ext_diag _ _ hP hQ (funext fun v=> ?_)
   obtain ⟨A,hA⟩:=wave_sum_rep v
   rw [←op_eq v,←op_eq v,←hA,map_sum,map_sum,map_sum,map_sum]
   simp_rw [(ContinuousLinearMap.sum_apply),hPair]


end YM.UVExt.Paths.Covering
