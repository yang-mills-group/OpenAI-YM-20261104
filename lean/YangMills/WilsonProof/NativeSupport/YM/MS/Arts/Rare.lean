import YM.MS.Arts.Rare
import YM.MS.Arts.MapA
/-!
# Stray leg vanishes by rotating on a prefix-stabilizing dimension

Flux traces entering affine-in-$D$. First use on higher-dimensional integer lines,
 rotation. Handles lone stray, double strays and covariance traces. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Pilot Spin
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{C A:Type}[Fintype A][DecidableEq A][Fintype C][DecidableEq C]
-- one extended vector slot
variable {X:Spin A}{i j k:A}{z:ℝ}
lemma cols (h:X.turn (spray i)=z • spray j) (f)(s:Bool)(c:C)(l:Legs (Mode (Leg A C) (Momentum A)))(p:Momentum A): beam (leggo C X) f ((vleg s i c,p)::l)=(z:ℂ) * beam (leggo C X) (D (vleg s j c,X.turn p) f) l:= by
    change (leggo C X).beam f ((((some i,s),c),p)::l)=_; rw [fromV]; unfold profile; rw [h]; simp [spray,Pi.single_apply,vleg,apply_ite,ite_mul]
omit [Fintype C] in lemma p_head (s:Bool) (c:C)(i j:A): X.prop (vleg s i c) (vleg s j c)=X.profile i j:= by simp only [prop,vleg,rayS, shadow,if_true]
omit [Fintype C] in
lemma p_side (s:Bool)(c:C)(a:Leg A C)(h:X.turn (spray i)=z • spray j)(hp:a≠vleg s j c) : X.back.prop a (vleg s i c)=0:= by
    rcases a with ⟨⟨_|a,t⟩,b⟩; simp [prop,rayS,shadow,vleg]; by_cases hC:b=c; swap; · simp [prop,vleg,hC];
    by_cases hv:t=s; swap; · simp [prop,vleg,rayS,hv];
    subst c t; change X.back.prop (vleg s a b) (vleg s i b)=0; rw [show X.back.prop _ _=_ from p_head s b a i (X:=X.back), ← X.dual i a]; have hx:a≠j:= fun ha=>hp (by rw [ha]; rfl); unfold profile; rw [h]; simp [spray,hx]
lemma trace_leg {K:Flux (Leg A C) (Momentum A) ℂ}{w:ℝ}(hk: Transport (leggo C X.back) K K) {t:A}(f g:Bool)(c d:C) (H:X.turn (spray i)=z • spray j)(h:X.turn (spray t)=w • spray k)(x:Momentum A): K (vleg f i c) (vleg g t d) x=(z:ℂ)*(w:ℂ)*K (vleg f j c) (vleg g k d) (X.turn x):= by
    have hx := hk (X.turn x) (vleg f i c) (vleg g t d); let Y:= K (vleg f j c) (vleg g k d) (X.turn x); let Q:= leggo C X.back; have hv : Q.volp (X.turn x) = x:= rear X; rw [hv] at hx; rw [hx,Finset.sum_eq_single (vleg f j c),Finset.sum_eq_single (vleg g k d)];
    · change K _ _ _* X.back.prop _ _ * X.back.prop _ _=_; rw [p_head,p_head,← X.dual i j,← X.dual t k]; unfold profile; rw [H,h]; simp [spray]; ring
    · intro i' ht hp; exact mul_eq_zero_of_right _ (p_side g d i' h hp)
    · simp
    · intro a _ ha; exact Finset.sum_eq_zero fun i _=> mul_eq_zero_of_left (mul_eq_zero_of_right _ (p_side _ _ _ H ha)) _
    · simp
-- trace_leg unnecessary? to prove trc affine, need equal even with K rotated same directions. use explicit.
variable {b:Bool}{m n:ℕ}{F:Mob G}(h:m≤n)
-- fix any or all dims on prefix
lemma beam_wide (X:Spin (L n))(hx:∀ p,X.turn (Left h p)=Left h p)(V:Rack G n) (l:Legs (Shore G m)) (s:Legs (Shore G n)): beam (flagS X G) V (lift h l ++ s)= beam (flagS X G) (fun r=> V (lift h l++r)) s:= by
    induction l generalizing V with
    | nil=> rfl -- not defeq?
    | cons a l ih=> rcases a with ⟨⟨⟨_|a,z⟩,c⟩,p⟩
                    · change (leggo _ X).beam V ((((none,z),c),Left h p)::(lift h l++s))=_; rw [fromG,hx]; exact ih (Koszul.D _ V)
                    have he : X.turn (spray (rises h a))=(1:ℝ) • spray (rises h a):= fixedBasis h hx a |>.trans (one_smul ..).symm -- argument
                    change (leggo _ X).beam V ((vleg z (rises h a) c,Left h p)::(lift h l++s))=_; rw [cols he,Complex.ofReal_one,one_mul,hx]; exact ih (Koszul.D _ V)
lemma beam_only (X:Spin (L n))(hx:∀ p,X.turn (Left h p)=Left h p) (V:Rack G n)(l:Legs (Shore G m)): beam (flagS X G) V (lift h l) = V (lift h l):= by simpa using beam_wide h X hx V l []
lemma vanish_one (H: Sturdy b F)(a s:Legs (Shore G m))(i:Apart m n)(p:SectorP m)(c:G.ColorIndex)(d:Bool): F n (lift h a ++ (vleg d (aside h i) c,Left h p)::lift h s)=0:=by
    let K:= Spin.spark (aside h i); let V:=flagS K G; have hx:= lightOn h i; have he : V.beam (F n)=F n:=H.turn n K (fixedLeft h hx); let l:= lift (G:=G) h a; let W:Shore G n:=(vleg d (aside h i) c,Left h p)
    have hc := sees_p (aside h i); have hT : K.turn (spray (aside h i))=(-1:ℝ) • spray (aside h i):= hc.trans (by simp)
    obtain hm := congr_fun he (l++W::lift h s); rw [beam_wide h K hx] at hm; unfold W flagS at hm; rw [cols hT (C:=G.ColorIndex) _ d c _ (Left h p), show K.turn _=Left h p from hx _, show (leggo _ K).beam _ (lift h s)= _ from beam_only h K hx _ s] at hm; simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul, at_D] at hm; exact neg_eq_self.mp hm
end YM.MS.Arts
