import YM.MS.Pearl.Gloss
/-!
# Aura at poles preserved via limits in subspaces

Real dimension condition independent off Course. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real Polynomial
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W Y F: Mob G} {x:ℂ} {b:Bool} {n ℓ m:ℕ} {h:ℕ} {f g:ℂ→ Mob G}
-- p-axis η
abbrev realDotty := 𝓝[≠] (0:ℝ)
def realAlong (v:ℂ→Mob G)(P:LeanR G): Prop:=∀ᶠ i:ℝ in realDotty,v i∈P
abbrev To (v:ℂ→Mob G)(P:LeanC G): Prop:=∀ᶠ i in dotty,v i∈P
lemma shoreC (P:LeanC G)(hv:Need P)(h:Pick n f F)(he:To f P): F ∈ P:= by
    induction n generalizing f with
    | zero=> exact hv.touch (Lift.wind h) he
    | succ n ih=> obtain ⟨H,hH,h⟩:=h; have hu:H∈P:= hv.touch (Lift.wind hH) he; exact ih h (he.mono fun j hx => P.smul_mem j⁻¹ (P.sub_mem hx hu))
lemma shoreR (P:LeanR G)(hv:Will P)(h:Pick n f F)(he:realAlong f P): F∈ P:= by
    have hk{f:ℂ→Mob G}{F:Mob G}(h:Lift f F)(he:realAlong f P): F∈P:= hv.touch (I:=ℝ) (f:=fun t:ℝ=> f t) (fun m l=> ( Lift.wind h m l).comp dotty_touch) he; -- type metavars
    induction n generalizing f with
    | zero=> exact hk h he
    | succ n ih=>
       obtain ⟨H,hH,h⟩:=h; have hx:= hk hH he; refine ih h (Eventually.mono he (fun i hi=>?_)); unfold slip; rw [← Complex.ofReal_inv,reality]; exact P.smul_mem i⁻¹ (P.sub_mem hi hx)
lemma priceC (P:LeanC G)(hv:Need P)(ht:altitude m f)(he:To f P)(y:ℝ) : priceY n m ℓ f y ∈ P := P.sum_mem fun _ _=> P.smul_mem _ (shoreC P hv ( Rub ht _) (he.mono fun _ hi=> P.smul_mem _ hi))
lemma priceR (P:LeanR G)(hv:Will P)(ht:altitude m f)(he:realAlong f P)(y:ℝ) : priceY n m ℓ f y ∈ P:= by
   unfold priceY; apply P.sum_mem; intro j hi; have hz : realAlong (paid m f) P:= by apply Eventually.mono he; intro i hi; unfold paid; rw [← Complex.ofReal_pow,reality]; exact P.smul_mem _ hi
   have he(t:ℝ): ley ℓ j t= (( (t*gNat ℓ)^j/(j.factorial:ℝ):ℝ):ℂ):= by simp [ley];
   rw [he y,reality]; exact P.smul_mem _ (shoreR P hv (Rub ht _) hz)
-- Pure pole algebra pointwise
lemma coolC (M: Mob G→ₗ[ℂ] Mob G)(h:Cool f): Cool (fun i=> M (f i)):= by
    refine Submodule.span_induction (p:=fun x _=> Cool fun i=> M (x i)) ?_ (by simp; exact (cone G).zero_mem) ?_ ?_ h;
    · rintro x ⟨n,hn,F,rfl⟩; simp_rw [Ice,map_smul]; exact iceC _ n hn
    · intro f g H H' hx hy; simp_rw [Pi.add_apply,map_add]; exact (cone G).add_mem hx hy
    intro c f H hx; simp_rw [Pi.smul_apply,map_smul]; exact (cone G).smul_mem c hx
lemma coolPair (M:Oceans.Pair G)(h:Cool f)(hp:Cool g): Cool (fun i=> M (f i) (g i)):= by
   refine Submodule.span_induction (p:=fun f _=> Cool fun i=> M (f i) (g i)) ?_ (by simp; exact (cone G).zero_mem) ?_ ?_ h ;
   · rintro x ⟨n,hn,F,rfl⟩; refine Submodule.span_induction (p:=fun x _=> Cool fun i=> M (Ice n F i) (x i)) ?_ (by simp; exact (cone G).zero_mem) ?_ ?_ hp
     · rintro y ⟨m,hm,V,rfl⟩; unfold Ice; simp_rw [ map_smul,LinearMap.smul_apply, ← mul_smul,← pow_add]; exact iceC _ _ (by omega)
     · intro x y hx hY h0 h1; simp_rw [Pi.add_apply,map_add]; exact (cone G).add_mem h0 h1
     intro c x H h; simp_rw [Pi.smul_apply,map_smul]; exact (cone G).smul_mem c h
   · intro x y hx hy hV hG; simp_rw [Pi.add_apply,map_add, LinearMap.add_apply]; exact (cone G).add_mem hV hG
   intro c x hx hG; simp_rw [ Pi.smul_apply,map_smul,LinearMap.smul_apply]; exact (cone G).smul_mem c hG
lemma coolEdge (w:Legs (Shore G m))(h:Cool f)(he:Tendsto (fun i=> f i m w) dotty (𝓝 x)): ∀ z:ℂ,f z m w=0:= by
   classical
   let L: Mob G→ₗ[ℂ] Mob G:={toFun := fun i _ _=>i m w,map_smul':=fun _ _=> rfl,map_add':=fun _ _=>rfl}; intro z; obtain he:= deep_zero (coolC L h) (F:=fun _ _=>x) (fun i p=> he); exact congr_fun (congr_fun (congr_fun he z) m ) w
end YM.MS.Pearl
