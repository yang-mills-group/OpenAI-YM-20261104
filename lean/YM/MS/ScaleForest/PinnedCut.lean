import YM.MS.ScaleForest.Rephase
/-!
# Between-pin half-line join, with literal contractions, preserving open planes

This uses the unintegrated kernel (including at dimension z), before any IR
limit. Momentum not fixed when gluing two components both with sources.
Verify the full z-dependent spin prescription in the integrated version later.
In particular there is a simplification of the tensor-valued dimensional-rule
`ScaleForest.innerTrace` for this join (only this kind, not closing a loop):
`yeast` not needed here, because on a test plane there can't be glue with just
one leg sticking out of it on a child. We prove this for ARBITRARY sturdy
inputs (which we'll be able to use also in the quotient for a pole
insertion). Also show `symmetricCut` is literally the cross in `Wtr`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff
variable {G : Gauge} {s : ℂ} {K : Rip G} {X Y : Mob G} {m n : ℕ}

def oneCross (K : Rip G) (X Y : Mob G) (q : SectorP m) (i j : Cfield G m) : Shared (Shore G m) ℂ := fun l r=>
   K m i j q * (cross (parity j) (degree (field parity) l) * X m ((i,q)::l)) * Y m ((j,-q)::r)
def cutTree (K : Rip G) (X Y : Mob G) (q : SectorP m) (u : Legs (Shore G m)) : ℂ:=
   scatter (field parity) u (∑ i, ∑ j, oneCross K X Y q i j)

/-- The other orientation will eventually have the *same integral*. Include
both at finite-regulated force. -/
def symmetricCut (K : Rip G) (X Y : Mob G) (q : SectorP m) (u : Legs (Shore G m)) := cutTree K X Y q u+cutTree K X Y (-q) u

section orientation
variable (he : closedF K false) (ht : reverseF K) (X Y : Mob G) (q : SectorP m)
   (i j : Cfield G m) (w : Legs (Shore G m))

include ht
theorem switchDirs (l r : Legs (Shore G m)) :
    oneCross K X Y (-q) j i l r = K m i j q * D (j,-q) (sign (field parity) (parity i) (X m)) l * Y m ((i,q)::r) := by
   unfold oneCross; rw [neg_neg, ht m]; simp_rw [at_D,at_sign,degree_cons]; change _= K m i j q * (cross (parity i) ((parity j) ^^ degree (field parity) l) *_) * _
   rw [cross_right (parity i) (parity j),cross_comm (parity i) (parity j)]; ring
include he
theorem symmetricPath : K m i j q * link (diffPair (i,q) (j,-q)) false (field parity) (X m) (Y m) w=
    scatter (field parity) w (oneCross K X Y q i j + oneCross K X Y (-q) j i) := by
   let Q:= allocate (field parity) w (R:=ℂ)
   have hu : oneCross K X Y q i j+oneCross K X Y (-q) j i =
       K m i j q • ((fun l r=> sign (field parity) (parity j) (D (i,q) (X m)) l * D (j,-q) (Y m) r) +
       fun l r=> D (j,-q) (sign (field parity) (parity i) (X m)) l * D (i,q) (Y m) r ) := by
      funext l r; simp only [Pi.add_apply,Pi.smul_apply, smul_eq_mul,mul_add, switchDirs ht]; unfold oneCross; simp only [at_D,at_sign]; ring
   rw [hu]
   by_cases h: K m i j q=0
   · rw [h,zero_mul,zero_smul]; exact (map_zero Q).symm
   rw [link_pair (i,q) (j,-q) (p:=field parity) (he m i j q h)]
   simp only [Pi.add_apply,scattered]
   simp_rw [show ∀ f:Shared (Shore G m) ℂ, scatter (field parity) w f= Q f from fun _=>rfl, map_smul, map_add]; rfl

theorem Wick_between : symmetricCut K X Y q = link (trc (K m) q) false (field parity) (X m) (Y m) := by
   funext u; simp only [symmetricCut,cutTree,trc,link_sum, link_scale, Finset.sum_apply, Pi.smul_apply,smul_eq_mul]; simp_rw [symmetricPath he ht];
   let Q:= allocate (field parity) u (R:=ℂ)
   simp_rw [show ∀ f:Shared (Shore G m) ℂ, scatter (field parity) u f= Q f from fun _=>rfl, map_sum, map_add, Finset.sum_add_distrib]; nth_rw 2 [Finset.sum_comm];

variable (h : m≤n) (u : Legs (Shore G m))
omit he ht
-- plane growth by the sturdy (stamped) inputs
variable (hx : Sturdy false X) (hy : Sturdy false Y) (hK : Ruddy false K)
include hx hy hK
theorem cut_grow : cutTree K X Y (Left h q) (Arts.lift h u)=cutTree K X Y q u:= by
   unfold cutTree; rw [Arts.scatter_up]; refine scatter_congr _ _ _ _ fun l r hw=>?_
   let V:= embA (rises h) (C:=G.ColorIndex)
   let W (i: Apart m n)(p:Bool)(c:G.ColorIndex):= vleg p (aside h i) c
   let M(i j:Cfield G n) := oneCross K X Y (Left h q) i j (Arts.lift h l) (Arts.lift h r)
   have h_l (i p c)(j : Cfield G n) : M (W i p c) j=0:= by unfold M oneCross; rw [show X n ((W i p c,Left h q)::Arts.lift h l)=_ from vanish_one h hx [] l i q c p]; ring
   have h_r i j p c: M i (W j p c)=0:= by unfold M oneCross; rw [← map_neg,show Y n ((W j p c,Left h (-q))::Arts.lift h r)=_ from vanish_one h hy [] r j (-q) c p]; ring
   have h_v (i j : Cfield G m) : M (V i) (V j)=oneCross K X Y q i j l r := by
      unfold M oneCross V; rw [lifts_degree,risesP,hK.grows, ← map_neg]; rw [← hx.grows h ((i,q)::l),← hy.grows h ((j,-q)::r)]; rfl
   simp only [Finset.sum_apply]; rw [show (∑ i: Cfield G n, ∑ j,M i j)=_ from Arts.more h _];
   simp_rw [show ∀ i,(∑ j,M i j)=(∑ j,M i (V j))+(∑ p:Apart m n,∑ s,∑ c, M i (W p s c)) from fun i=> more h _];
   change (∑ i, ((∑ j, M (V i) (V j))+(∑ p: Apart m n,∑ s,∑ c, M (V i) (W p s c)))) + (∑ p:Apart m n,∑ s,∑ c,((∑ j,M (W p s c) (V j))+(∑ p':Apart m n,∑ t,∑ d,M (W p s c) (W p' t d)))) = _
   simp only [h_r,h_l,h_v, Finset.sum_const_zero,add_zero]
include he ht

def references (z:ℂ)(K : Rip G)(X Y : Mob G)(q : SectorP m) := Wtr z K (weave X Y) q -
    product (field Landau.parity) (Wtr z K X q) (Y m) - product (field Landau.parity) (X m) (Wtr z K Y q)

omit he ht hx hy hK in
private theorem lift_multip (f v:Rack G m) (F V:Rack G n) (hF:∀ w,F (Arts.lift h w)=f w) (hV:∀ w,V (Arts.lift h w)=v w):
    product (field parity) F V (Arts.lift h u) = product (field parity) f v u := by simp only [scattered,Arts.scatter_up,hF,hV]

include h in
theorem references_at_n : references n K X Y q u = symmetricCut K X Y q u := by
   rw [← show symmetricCut K X Y (Left h q) (Arts.lift h u) = symmetricCut K X Y q u from ?_]
   · unfold references; rw [Pi.sub_apply,Pi.sub_apply, tallyN (weave_token hx hy) hK h,Wick_between he ht];
     unfold link; rw [sign_id]; simp only [Pi.sub_apply];
     rw [ lift_multip h u (Wtr n K X q) (Y m) (trc (K n) (Left h q) (X n)) (Y n) (fun _=> (tallyN hx hK h).symm) (hy.grows h),
       lift_multip h u (X m) (Wtr n K Y q) (X n) (trc (K n) (Left h q) (Y n)) (hx.grows h) (fun _=> (tallyN hy hK h).symm)]
     rfl
   unfold symmetricCut; rw [← map_neg,cut_grow X Y q h u hx hy hK,cut_grow X Y (-q) h u hx hy hK]

theorem z_cross (s : ℂ) : references s K X Y q = symmetricCut K X Y q := by
   let Q(z:ℂ):=references z K X Y q
   have hh : Q s=Q (m:ℂ)+(s-m) • (Q (m+1:ℕ)-Q m):= by
     unfold Q references; simp only [Arts.combo s m,map_add,map_sub,map_smul, LinearMap.add_apply, LinearMap.sub_apply,LinearMap.smul_apply]; module
   change Q s=_; rw [hh, show Q (m:ℂ)=_ from funext (fun w=> references_at_n he ht X Y q le_rfl w hx hy hK), show Q (m+1:ℕ)= _ from funext (fun w=> references_at_n he ht X Y q (Nat.le_succ _) w hx hy hK), sub_self,smul_zero,add_zero]

end orientation
end YM.MS.ScaleForest
