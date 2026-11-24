import YM.RG12.Strike.Chisels
/-!
# Angular formula for two vertex-to-mark contracted lines at resonant Taylor charge

Weights radial and annular. Includes possible derivative leg. Uses only ordinal stencil of
Euclidean Feynman normalized line (for Landau need curl contraction adapter), summing multiple
orientation before calling readers via linearity. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {w:R→ℂ}
structure Dried (w:R→ℂ) : Prop extends Round w where
    near : w =ᶠ[𝓝 0] 0
variable (h:Dried w)
-- continuous multiplied by annular. reuse
include h
lemma withered (f:R→ℂ)(he:∀ x:R,x≠0→ ContinuousAt f x):Annular (w*f):=by
   refine ⟨continuous_iff_continuousAt.mpr (fun x=> ?_), h.compact.mul_right⟩
   by_cases hx:x=0
   · subst x; have hf:w*f=ᶠ[𝓝 (0:R)] (fun _=>0):=by filter_upwards [h.near] with x hx; simp only [Pi.mul_apply,hx,Pi.zero_apply,zero_mul]
     exact (continuousAt_const).congr hf.symm
   exact h.continu.continuousAt.mul (he x hx)
lemma closed (k:ℕ)(c:ℂ): Round (fun x=> w x*(c*(black x)^k)⁻¹):=by
   refine Round.mk (withered h _ (fun x hx=>?_)) ?_
   · by_cases hc:c=0
     · simp [hc, continuousAt_const]
     have hz:black x ≠ 0 :=by unfold black; exact_mod_cast (show (‖x‖^2:ℝ) ≠ 0 by positivity [norm_pos_iff.mpr hx])
     apply ContinuousAt.inv₀ (show ContinuousAt (fun x=>c*black x^k) x from ?_) (show (fun x=>c*black x^k) x≠0 from mul_ne_zero hc (pow_ne_zero k hz)); unfold black; fun_prop
   intro U x; unfold black; simp [h.iso]
lemma dressed (a b:Stroke): Round (fun x => w x * (black x ^ a.rate)⁻¹*(black x^b.rate)⁻¹):=by
   convert closed h (a.rate+b.rate) 1 using 1
   ext1 x; rw [one_mul,pow_add]; simp [mul_assoc]; exact Or.inl (by ring)
lemma pour (P:Cells→ℂ)(n:ℕ)(a b:Stroke): Integrable (fun x:R=>w x * fall (gauge n P) x * (drip a x *drip b x)):=by
   convert weighted _ (dressed h a b).toAnnular (f:=fun x=>fall (gauge n P) x * (a.weight *sun a.deck x * (b.weight*sun b.deck x))) ((fall_cont ..).mul ((continuous_const.mul (sun_cont _)).mul (continuous_const.mul (sun_cont _)))) using 1
   ext1 x; unfold drip; ring
local notation "jet"=>fun (P:Cells→ℂ) (n:ℕ) => fall (gauge n P)
lemma pairing_below (P:Cells→ℂ)(n:ℕ)(a b:Stroke)(hP: Rated n P)(ht:a.deck.length+b.deck.length < n):
    (∫ x:R,w x * fall (gauge n P) x * (drip a x *drip b x))=0:=by
   obtain ⟨d,h⟩:= shave (dressed h a b) n
   have he:=h P hP (a.deck++b.deck) (by rw [List.length_append]; exact ht.le); rw [if_neg (by rw [List.length_append]; exact ht.ne)] at he
   let v(x:R):= w x * (black x ^ a.rate)⁻¹ * (black x ^ b.rate)⁻¹ * fall (gauge n P) x * sun (a.deck++b.deck) x
   rw [show (fun x:R=> w x * _ * (drip a x*drip b x)) = fun x=> (a.weight*b.weight)*v x from funext fun x=>by unfold v drip; rw [← sun_join]; ring,
      MeasureTheory.integral_const_mul,show ∫ x,v x = 0 from he,mul_zero]
lemma pairing_hold (m n:ℕ) :∃ c:ℂ,∀ P:Cells→ℂ, Rated (m+n) P→∀ a b:Cells,a.length=m→b.length=n→
    (∫ x:R,w x * fall (gauge (m+n) P) x * (drip (pin a) x *drip (pin b) x))=c*P (a++b):=by
   obtain ⟨d,h⟩:= shave (dressed h ⟨1,m+1,[]⟩ ⟨1,n+1,[]⟩) (m+n)
   refine ⟨coefficient m * coefficient n * d,fun P hP a b ha hb=>?_⟩
   have ht:(a++b).length=m+n:=by simp [ha,hb]
   have he:=h P hP (a++b) ht.le; rw [if_pos ht] at he
   let v(x:R):= w x * (black x^(m+1))⁻¹ * (black x^(n+1))⁻¹ * fall (gauge (m+n) P) x *sun (a++b) x -- implicit underscore
   rw [show (fun x:R=> w x *fall (gauge (m+n) P) x * (drip (pin a) x*drip (pin b) x)) = fun x=> (coefficient m*coefficient n)*v x from ?_,MeasureTheory.integral_const_mul,show ∫ x,v x =_ from he]; ring
   funext x; unfold v drip pin;rw [ha,hb, ←sun_join];ring

lemma pours (P:Cells→ℂ) (n:ℕ)(a:Stroke)(B:List Stroke): Integrable (fun x:R=>w x* fall (gauge n P) x* (drip a x*scripts B x)):=by
   induction B with
   | nil=>simp [scripts]
   | cons b B Hb=>simpa only [scripts_step,mul_add] using! (pour h P n a b|>.add Hb)
lemma pour_table (P:Cells→ℂ) (n:ℕ)(A B:List Stroke):Integrable (fun x:R=>w x* fall (gauge n P) x *(scripts A x* scripts B x)):=by
   induction A with
   | nil=> simp [scripts]
   | cons a A hA=> simpa only [scripts_step,add_mul,mul_add] using! (pours h P n a B|>.add hA)
lemma toss_up (P:Cells→ℂ)(n:ℕ) (A B:List Stroke)
    (he:∀ a∈ A,∀ b∈B, a.deck.length+b.deck.length < n)(hz:Rated n P):
      (∫ x:R,w x* fall (gauge n P) x * (scripts A x* scripts B x))=0:=by
   let q(x):= w x *fall (gauge n P) x
   induction A with
   | nil=>simp [scripts]
   | cons a A Ha=>
     simp_rw [scripts_step,add_mul,mul_add];rw [integral_add (pours h P n a B) (pour_table h P n A B),Ha (fun b hb=>he b (List.mem_cons_of_mem a hb)),add_zero]
     have he':=he a List.mem_cons_self
     clear he Ha
     induction B with
     | nil=>simp [scripts]
     | cons b B Hb=>
       simp_rw [scripts_step,mul_add]; rw [integral_add (pour h P n a b) (pours h P n a B),Hb (fun c hc=> he' c (List.mem_cons_of_mem b hc)),pairing_below h P _ a b hz (he' b List.mem_cons_self),add_zero]
-- launch joint column. VALID at every true annulus scale BEFORE limits.
theorem workbench (n m:ℕ): ∃ c:ℂ,∀ P:Cells→ℂ,Rated (n+m) P→∀ L K:Cells, L.length=n→K.length=m→
    (∫ x:R,w x * fall (gauge (n+m) P) x *(barrage field L x * barrage field K x))=c*P (L++K):=by
   obtain ⟨c,H⟩:=pairing_hold h n m; refine ⟨c,fun P hP L K hL hK=>?_⟩
   obtain ⟨A,hA,f⟩:= fire L; obtain ⟨B,hB,g⟩:= fire K
   let q:=gauge (n+m) P
   let F(x:R):=w x*fall (gauge (n+m) P) x
   have hk:w 0=0:=h.near.eq_of_nhds
   let J(a b:R→ℂ)(x:R):= F x*(a x*b x); let a:=pin L;let b:=pin K
   have he:J (barrage field L) (barrage field K)=fun x=> J (drip a) (drip b) x + J (drip a) (scripts B) x + J (scripts A) (scripts (b::B)) x:=by
      funext x; unfold J F; by_cases hx:x=0; simp [hx,hk]; rw [f x hx,g x hx,scripts_step,scripts_step]; unfold a b;ring
   change ∫ x,J _ _ x=_;rw [he,integral_add,integral_add]
   · have hr: ∀ x∈[a],∀ y∈B,x.deck.length + y.deck.length < n + m:=by
        intro x h₁ y h₂
        have hz:x=a:=List.mem_singleton.mp h₁; rw [hz]; change L.length+_ <_; have ht := hB y h₂;omega
     have hu: ∀ x∈A,∀ y∈b::B,x.deck.length+y.deck.length < n+m:=by
        intro x h₁ y h₂; have hx:=hA x h₁
        rcases List.mem_cons.mp h₂ with rfl|h₂
        · change _+K.length<_;omega
        have h:=hB y h₂;omega
     rw [show ∫ x,J _ (scripts B) x=0 from by simpa [scripts_step,scripts] using! (toss_up h P _ [a] B hr hP), show ∫ x,J (scripts A) _ x=0 from toss_up h P _ _ _ hu hP,add_zero,add_zero]; exact H P hP L K hL hK
   · exact pour h ..
   · exact pours h ..
   · exact (pour h P (n+m) a b).add (pours h ..)
   exact pour_table h ..
end YM.RG12.Strike
