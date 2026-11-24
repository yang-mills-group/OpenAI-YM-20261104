import YM.RG12.Strike.Lore
/-! # Pair rule on any radial annulus

Index basis directions by strings. Use the diagonal polarization derivative rather
than the dimensionally regulated Ward averages (the current computations specialize
literally to 4 Euclidean dimensions, no evanescent projections).
 -/
set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff BigOperators InnerProductSpace Classical
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Finset Equiv
variable {α:Type}[Fintype α]{m:ℕ}
abbrev Lay (m:ℕ)(α:Type):= (Bool × Fin m)≃α
abbrev Ribbon := α → R
abbrev through (x:R)(y:R):ℂ:= ↑⟪x,y⟫_ℝ
abbrev a (L:Lay m α)(u : Fin m):α := L (false,u)
abbrev b (L:Lay m α)(u : Fin m):α := L (true,u)
def period (L:Lay m α)(v:α→R) := ∏ i:Fin m, through (v (a L i)) (v (b L i))
omit [Fintype α] in
lemma tall (L:Lay m α) : Continuous (period L):= by unfold period through; fun_prop
section bills
variable [DecidableEq α] (L:Lay m α)
-- universal rewrite at a terminal to manage updates in `linear` below
omit [Fintype α] [DecidableEq α] in
lemma torn (c:Bool)(i:Fin m)(v u:α→R)
    (h:∀ j:α,j ≠ L (c,i) → u j=v j) :
   period L u=through (u (a L i)) (u (b L i))*∏ j∈univ.erase i, through (v (a L j)) (v (b L j)):=by
   unfold period; rw [← mul_prod_erase _ _ (mem_univ i)]; apply congrArg (fun t=> _ * t); refine prod_congr rfl ?_; intro j hj; have he:= ne_of_mem_erase hj
   rw [show u (_)=v (a L j) from h _ (by exact fun hx=>he (congr_arg Prod.snd (L.injective hx))), show u (b L j)=_ from h _ (by exact fun hx=>he (congr_arg Prod.snd (L.injective hx)))]
def polar : ContinuousMultilinearMap ℝ (fun _:α=>R) ℂ where
   toFun:=period L
   map_update_add' v i y z:=by
      obtain ⟨⟨c,i⟩,rfl⟩:=L.surjective i
      let f(z):=update v (L (c,i)) z
      let B:=∏ j∈univ.erase i, through (v (a L j)) (v (b L j))
      have hh (z):period L (f z)=through (f z (a L i)) (f z (b L i))*B:= torn L c i v _ (fun j hj=>update_of_ne hj ..)
      change period L (f (y+z))=period L (f y)+period L (f z);rw [hh,hh,hh]
      have he : a L i≠ b L i:=by unfold a b; exact (L.injective.ne (fun h=>Bool.noConfusion (congr_arg Prod.fst h)))
      cases c<;> simp only [f, b,a] at *
      · simp [he.symm, through,inner_add_left,add_mul]
      simp [he,through,inner_add_right,add_mul]
   map_update_smul' v i k z:=by
      obtain ⟨⟨c,i⟩,rfl⟩:=L.surjective i
      let f(z):=update v (L (c,i)) z
      let B:=∏ j∈univ.erase i, through (v (a L j)) (v (b L j))
      have hh (z):period L (f z)=through (f z (a L i)) (f z (b L i))*B:= torn L c i v _ (fun j hj=>update_of_ne hj ..)
      change period L (f (k • z))=k • period L (f z);rw [hh,hh]
      have he : a L i≠ b L i:=by unfold a b; exact (L.injective.ne (fun h=>Bool.noConfusion (congr_arg Prod.fst h)))
      cases c <;> simp only [f, b,a] at *
      · simp [he.symm,through,real_inner_smul_left,mul_assoc,Complex.real_smul]
      simp [he,through, real_inner_smul_right,mul_assoc, Complex.real_smul]
   cont:= tall L
-- choice of inst in Map update part overrides v binder. pass. 
omit [DecidableEq α] [Fintype α] in
lemma polar_at (x:α→R):polar L x=period L x:=rfl
end bills
abbrev P (α:Type*) := ContinuousMultilinearMap ℝ (fun _:α=>R) ℂ
variable [DecidableEq α] (w:R→ℂ)(hw:Round w)
-- seed L supplied by even Alpha card. sum over all perms of slot positions,
-- same as sum over all L. Cost λ independent. Compute even diagonal, odd case earlier.
def spoke (m:ℕ) (α:Type)[Fintype α][DecidableEq α]:P α := ∑ L : Lay m α,polar L
lemma spoke_at (x:α→R):spoke m α x=∑L:Lay m α,period L x:=by unfold spoke; rw [_root_.sum_apply]; rfl
lemma spoke_change (σ:Equiv.Perm α)(v:α→R):spoke m α (v ∘σ) = spoke m α v:= by
  let L : Equiv.Perm (Lay m α):={
     toFun x:= x.trans σ
     invFun x:=x.trans σ.symm
     left_inv _:=by ext; simp
     right_inv _:=by ext; simp
    }
  rw [spoke_at,spoke_at]; exact Fintype.sum_equiv L _ _ (fun _=>rfl)
lemma spoke_diag (k:R): spoke m α (fun _:α=>k)= (↑(Fintype.card (Lay m α)):ℂ) * (↑‖k‖:ℂ)^(2*m):=by
   rw [spoke_at]; unfold period
   simp [through,nsmul_eq_mul,pow_mul] -- simp redundancy
omit [DecidableEq α] in
lemma card (L:Lay m α): Fintype.card α=2*m:=by rw [← Fintype.card_congr L]; simp
include hw
theorem law (L: Lay m α) : ∃ c:ℂ,∀ v:α→R,
    (∫ x:R,bill w v x)= c * (∑ L:Lay m α, period L v):=by
   let c:ℂ:= duty w hw.toAnnular (fun _:α=> bar 0)/(↑(Fintype.card (Lay m α)):ℂ)
   let B:= c • spoke m α
   haveI : Nonempty (Lay m α):=⟨L⟩
   have hm:(↑(Fintype.card (Lay m α)):ℂ)≠0:= by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Lay m α)≠0)
   have he(x:α→R):B x=c * spoke m α x:=rfl
   have hx:duty w hw.toAnnular=B:= by
      apply unique _ B (uniform w hw.toAnnular) _ (fun v=>?_)
      · intro σ v; rw [he,he,spoke_change]
      rw [he,spoke_diag,duty_diag w hw v 0,card L]; unfold c; field_simp

   refine ⟨c,fun v=>?_⟩
   rw [← duty_at w hw.toAnnular v,hx,he,spoke_at]
omit [DecidableEq α] in
lemma void (h:Odd (Fintype.card α))(v : α →R) : (∫ x:R,bill w v x)=0 := by
   have he:(duty w hw.toAnnular : P α)=0:=unique _ 0 (uniform w hw.toAnnular) (by intro; simp) (fun v=> by rw [odd_lore w hw v h]; rfl)
   rw [← duty_at w hw.toAnnular v,he]; simp
-- structured version over arbitrary finite pool of Taylor axes labeled externally
lemma coins {m:ℕ}(L:Lay m α): ∃ c:ℂ,∀ v:α→ Axis4,
    (∫ x:R,w x * ∏ i:α, (x (v i) :ℂ))=c*(∑ L:Lay m α,∏i:Fin m, if v (a L i)=v (b L i) then (1:ℂ) else 0):=by
   obtain ⟨c,h⟩:=law w hw L
   refine ⟨c,fun v=>?_⟩
   specialize h (bar∘v); unfold bill period at h; dsimp only [Function.comp_apply] at h
   simp_rw [through,dot_bar] at h
   simpa only [project,apply_ite (fun x:ℝ=>(x:ℂ)),Complex.ofReal_one,Complex.ofReal_zero] using h
end YM.RG12.Strike
