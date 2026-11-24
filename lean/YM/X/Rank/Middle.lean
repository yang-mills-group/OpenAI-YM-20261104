import YM.X.Rank.Path
/-! Joint two-leg residue. Constructive separation of flavor and color ambiguity at
  any weight, using observable (color-paired) probes only. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial Rad
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Finset E4} {a b m d v u : E4}(c : G.ColorIndex)

lemma slit_patch (f:Stroke→ℂ)(k:G.ColorIndex)(a b:Scout) : slit (dip f k) (patch a b)= C (bill a.1 a.2 f)*torch b k + C (bill b.1 b.2 f)*torch a k:= by
  rw [patch, _root_.map_sum,Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
  · simp only [Derivation.leibniz,slit_torch,↓reduceIte,smul_eq_mul]; ring
  intro i _ hi; rw [Derivation.leibniz,slit_torch,slit_torch]; simp [hi]
lemma slit_dark (f:Stroke→ℂ)(k:G.ColorIndex){p:Canvas G}(h:∀ i:Fiber G, i∈p.vars→ f i.1=0): slit (dip f k) p=0:= by
  apply MvPolynomial.derivation_eq_zero_of_forall_mem_vars; intro i hi; rw [slit_X]; simp [dip,h i hi]
private lemma slit_double (f:Stroke→ℂ)(k:G.ColorIndex)(a b:Scout)(p:Canvas G)(h:slit (dip f k) p=0) :
    let q:= slit (dip f k); let B:= bill a.1 a.2 f; let V:= bill b.1 b.2 f
    q (q (patch a a*(patch b b*p)))= C (2*B*B)*(patch b b*p) + C (2*V*V)*(patch a a*p) + C (8*B*V)*(torch a k*torch b k*p):= by
   intro q B V; unfold q B V; simp only [_root_.map_add, Derivation.leibniz,slit_patch,h,smul_eq_mul,slit_torch,slit_C,↓reduceIte, _root_.map_ofNat,map_zero,C.map_mul]; ring
private lemma slit_meter (t:ℂ)(i:G.ColorIndex)(z:Scout)(p:Canvas G): E c (slit (t • cost c i z) (slit (t • cost c i z) p))=
    t*t* E c (slit (cost c i z) (slit (cost c i z) p)) := by simp_rw [slit_smul,Derivation.map_smul,map_smul,smul_eq_mul];ring
lemma torch_supported (w:Scout)(X:Set (Fiber G))(hx:∀ i:Ax 0,∀ k:G.ColorIndex,(shell w.1 i,k)∈ X)(i:G.ColorIndex): torch w i ∈ MvPolynomial.supported ℂ X := by
   rw [torch_formula]; refine Subalgebra.sum_mem _ fun y _=> Subalgebra.mul_mem _ ?_ (X_mem_supported.mpr (hx ..)); exact (MvPolynomial.supported ℂ X).algebraMap_mem _
lemma patch_supported (w z:Scout)(X:Set (Fiber G))(hx:∀ i:Ax 0,∀ k:G.ColorIndex,(shell w.1 i,k)∈ X)(hy:∀ i:Ax 0,∀ k:G.ColorIndex,(shell z.1 i,k)∈ X): patch w z ∈ MvPolynomial.supported ℂ X := Subalgebra.sum_mem _ fun i (_:i∈Finset.univ)=> Subalgebra.mul_mem _ (torch_supported w X hx i) (torch_supported z X hy i)

abbrev Fits (S : Set E4)(p:Canvas G) := p∈ supported ℂ {i:Fiber G| i.1.1∈ S}
private lemma vanish (P : Canvas G)(z z':Scout) {y s:ℂ}(hy:y ≠ 0)(hs:s≠0) (he:E c (patch z z*P)=0)(hf:E c (patch z' z'*P)=0) (h:(∑ i:G.ColorIndex, E c (C (2*y*y)*(patch z' z'*P)+C (2*s*s)*(patch z z*P)+C (8*y*s)*(torch z i*torch z' i*P)))=0) : E c (patch z z' * P)=0 := by
   simp_rw [map_add,C_mul',map_smul,he,hf,smul_zero,zero_add,smul_eq_mul,← Finset.mul_sum] at h
   rw [patch, Finset.sum_mul,_root_.map_sum]; exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hy) hs)

lemma pole_zero (P : Canvas G) (hc:Fits (S:Set E4) P){z z':Scout}(hy:z.1=a)(hs:z'.1=b) (h: View S a b m d v)(w:Flavor 0)(f:Stroke→ℂ)(hp:∀ i:Stroke, i.1∈S→f i=0)(hH:∀ i:Stroke,MidOK S a b i→ Shine (shining c m d v w i) (f i))
    (hh: bill z.1 z.2 f≠0)(hh':bill z'.1 z'.2 f≠0)(he:E c (patch z z*P)=0)(hf:E c (patch z' z'*P)=0)
    (hz:∀ᶠ t:ℝ in atTop,E c (patch (penumbra m v w t) (penumbra m v w t)*(patch z z*(patch z' z'*P)))=0): E c (patch z z'*P)=0 := by
   let U:= patch z z*(patch z' z'*P); let s₀:= supported ℂ {x:Fiber G | MidOK S a b x.1}
   have hZ: ∀ t:Ax 0,∀ k:G.ColorIndex, MidOK S a b (shell z.1 t):= fun _ _=> Or.inr ⟨Or.inl hy,rfl⟩
   have hT: ∀ t:Ax 0,∀ k:G.ColorIndex, MidOK S a b (shell z'.1 t) := fun _ _=> Or.inr ⟨Or.inr hs,rfl⟩
   have hU : U∈s₀:= s₀.mul_mem (patch_supported z z _ hZ hZ) (s₀.mul_mem (patch_supported z' z' _ hT hT) (supported_mono (fun _ hu=>Or.inl hu) hc))
   let Y i (t:ℝ):= E c (slit (glint d v t • cost c i (penumbra m v w t)) (slit (glint d v t • cost c i (penumbra m v w t)) U))
   have h₁ i := twice_limit (dip f (G:=G) i) (fun t=>glint d v t • cost c i (penumbra m v w t)) (E c) U (fun j hj=>scaled_row c i w f j (hH j.1 (mem_supported.mp hU hj)))
   have ht (k:G.ColorIndex) : slit (dip f k) P=0:= slit_dark f k (fun i hi=>hp _ (mem_supported.mp hc hi))
   have hp': (fun t=>∑ i:G.ColorIndex,Y i t)=ᶠ[atTop] (fun _=>0):= by
     filter_upwards [hz] with t hh; unfold Y; simp_rw [slit_meter,← Finset.mul_sum, ← second_reads]; rw [show E c (patch _ _* U)=0 from hh,mul_zero]
   have hh := (Shine.respects (Shine.sum _ fun i _=>h₁ i) hp').separates (Shine.const 0)
   simp_rw [U, fun k=>slit_double f k z z' P (ht k)] at hh; exact vanish c P z z' (by assumption) hh' he hf hh
end YM.PositionX.Rank
