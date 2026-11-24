import YM.SchemeConversionRG11.FirstW.Due.Zero
/-! Simple measure kills all degree1 pol even off-shell Taylor extension. Critical here: Bare.walk uses unsorted `Finset.toList`; higher-index stars would need their own (possible additional mixing) proof. Only prove second-order jet convergence. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Set MeasureTheory Lattice Pert Align Position Deck Maxwell MvPolynomial
open scoped Classical BigOperators
variable {G:Gauge}{F:Labels.Frames G}{V:Type*}{d:ℕ}
lemma no_signals (hg:G.Simple) (j:ℕ)(p:Labels.Taylor G j →ₗ[ℝ] ℂ)(h:∀ (g:G.El)t,p (Labels.Taylor.paint g t)= p t)(q:Labels.Taylor G j): p q=0 := by
 let f : Bare.Response G j →ₗ[ℝ] ℂ:= p ∘ₗ Bare.radialMap
 have he (y:G.El)(x:Bare.Response G j): f (fun i a s=> G.adjoint y (x i a s))=f x:= by unfold f; simp only [LinearMap.comp_apply]; exact (congrArg p (Bare.radial_color y x)).trans (h y _)
 let I:= Fin j→Axis
 let L(i a:Axis)(s:I) : G.Color →ₗ[ℝ] Bare.Response G j:= LinearMap.single ℝ _ i ∘ₗ LinearMap.single ℝ _ a ∘ₗ LinearMap.single ℝ (fun _ : I=>G.Color) s -- placeholders
 have hQ(i a:Axis)(s:I)(C:G.Color): f (L i a s C)=0:= Extra.WeakScaling.Color.linear_invariant hg (f.comp (L i a s)) (fun u x=>by rw [LinearMap.comp_apply,show L i a s (G.adjoint u x)=(fun i' a' s'=> G.adjoint u (L i a s x i' a' s')) from ?_]; exact he u _; funext i' a' s'; by_cases e1:i'=i <;> by_cases e2:a'=a <;> by_cases e3:s'=s <;> simp [L,e1,e2,e3]) C
 let X:=Bare.components q
 have hx:Bare.radialMap X =q:=Bare.complete q
 have hv:X = ∑ i:Axis,∑ a:Axis,∑ s:I,L i a s (X i a s):=by
   funext i a s; simp only [L,Finset.sum_apply,LinearMap.comp_apply,LinearMap.single_apply]
   rw [Finset.sum_eq_single i]; swap; · intro b _ h; simp [Ne.symm h]
   · simp only [Pi.single_eq_same]; rw [Finset.sum_eq_single a]; swap; · intro b _ h; simp [Ne.symm h]
     · simp only [Pi.single_eq_same]; rw [Finset.sum_eq_single (s:I)]; simp; intro b _ h; simp [Ne.symm h]; simp
     simp
   simp
 calc p q=f X:= by unfold f; rw [LinearMap.comp_apply,hx]
      _=0:=by rw [hv]; simp only [map_sum,hQ, Finset.sum_const_zero]
lemma linear_spends (k:E F d)(a:Who G d)(hg:G.Simple): coeff 0 (D1 a (cloak F k))=0 := by
 let p := cloak F k
 let L:Dot G d →ₗ[ℝ] ℂ:= ∑ i:Who G d,(LinearMap.smulRight (LinearMap.proj i) (coeff 0 (D1 i p)))
 have h (x:Dot G d): L x= look 0 (windPrice x p):= by
    rw [show look 0 _= coeff 0 _ from MvPolynomial.aeval_zero' ((windPrice x) p),wind_val]; simp only [L,LinearMap.sum_apply, LinearMap.smulRight_apply,LinearMap.proj_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]; rfl
 let j:=a.val.1
 let B : Labels.Taylor G j →ₗ[ℝ] Labels.Jet G := LinearMap.single ℝ _ j
 let R:= L ∘ₗ salute d ∘ₗ B
 have he (u:G.El)(t:Labels.Taylor G j): R (Labels.Taylor.paint u t)=R t:= by
    have hp: L (salute d (B t))=L (paintL d u (salute d (B t))) := by rw [h,h]; have H:= strikes p p (paintL d u) (salute d (B t)) (fun x=>(tint F u x k).symm) 0; simpa only [map_zero] using H
    unfold R; simp only [LinearMap.comp_apply]; rw [hp,paintL,lit_any]; apply congrArg (L ∘ (salute d)); funext i; by_cases H:i=j; · subst i; simp [B]
    simp [B,H]
 have hw (v: Labels.Taylor G j): L (salute d (B v))=0:= no_signals hg _ R he _
 let A:= Labels.axes G j
 have perm: salute d (B (A a.val.2))=Pi.single a 1:=by
    funext b; rcases a with ⟨⟨a,i⟩,ha⟩; rcases b with ⟨⟨b,v⟩,hb⟩; unfold j at *; by_cases e:a=b
    · subst b; by_cases hi:v=i; · subst i; simp [j,salute,B,A]
      simp [j,salute,B,A,hi]
    simp [salute,B,j,e,Ne.symm]
 have he:= hw (A a.val.2); rw [perm] at he; simpa [L,p,Pi.single_apply,apply_ite] using he
lemma pder_end (k:E F 6)(a:Who G 6)(h:2<a.val.1)(hg:G.Simple) : D1 a (cloak F k)=0:= by
 refine MvPolynomial.ext _ _ fun s=> ?_; rw [coeff_zero]; by_cases e:s=0; · exact e.symm ▸ linear_spends _ _ hg
 by_contra hp; have he:= height_pass F k (leafup _ _ (MvPolynomial.mem_support_iff.mpr hp)); rw [map_add,Finsupp.weight_single,one_smul] at he; obtain ⟨b,hb⟩:=Finsupp.ne_iff.mp e
 have hh:= Finsupp.le_weight_of_ne_zero' fee (show s b≠0 from hb); unfold fee mass at *; omega
end YM.RG11.FirstW
