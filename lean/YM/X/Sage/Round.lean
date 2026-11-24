import YM.X.Sage.Song
/-!
# derivative lowering in orientation order. B and U using open-stencil degrees(accounting). symmetric measure. 
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V I:Type*} {q:ℕ+}{r R:ℝ}
local notation "Θ"=> Reed.Horizontal G
local notation "U"=> G.ColorIndex
local notation "P"=> Curly G
local notation "T"=> Tet
local notation "Λ"=> Foam G
local notation "o"=> side q k
abbrev veil (x:Cover)(k:ℕ) : Foam G→ₐ[ℂ] Curly G:= (dress (G:=G) x).comp (Pi.evalAlgHom ℂ (fun _:ℕ=> Curly G) k)
lemma veils (x:Cover)(p:Foam G): veil x k p=dress x (p k):= rfl
lemma veil_ξ (x:Cover)(p:T)(a:U): veil x k (ξ q r p a)=glyph (psiF q k x r p a):= pass_f ..
lemma veil_β (x:Cover)(p:T)(a:U): veil x k (βm q p a)=glyph (psiF q k x 1 p a):= veil_ξ x p a
lemma veil_μ (x:Cover)(p:T)(a:U): veil x k (μm q p a)=glyph (psiF q k x (-1) p a):= veil_ξ x p a
lemma veil_pot (x:Cover)(i:Axis)(a:U): veil x k (topA q i a)=glyph (psiA q k x i a):= pass_A ..
-- crown residue alphabet. key_type = curvature at x,h…
structure Beacon (q:ℕ+)(G:Gauge)(s:ℝ) where
   seed : Foam G
   shade : Tet → G.ColorIndex → Foam G
   light : ∀ p a, shade p a∈Ready q (Reed.Horizontal G)
   ridge (k:ℕ)(x:Cover)(f:Hair G→₀ℂ): edge (qu q G k) f (veil x k seed)= ∑ p:T,∑ a:G.ColorIndex,treats (qu q G k) f (psiF q k x s p a) • veil x k (shade p a)
local notation "Q"=> qu q G k
local notation "δ"=> edge Q
abbrev Offer (hβ:Beacon q G r):Foam G:= ∑ p:T,∑ a:U, bcomp q r p a * hβ.shade p a
-- beam
abbrev restU (q:ℕ+)(p:T)(a:U):= (2:ℂ) • μm q p a
def restB (q:ℕ+)(p:T)(a:G.ColorIndex):Foam G:= hook a (βm q (loop p)) (βm q (ℓ p))
lemma restB_s (p:T)(a:U): restB q p a∈ single (S:=Θ) q 2 (terminals G 1):= by
    unfold restB hook; refine (single q 2 _).sum_mem ?_; intro i _; refine (single q 2 _).sum_mem ?_; intro j _; refine (single q 2 _).smul_mem _ ?_; exact single_mulK (d:=1) (k:=1) rfl (degreeΦ (loop p) i) (degreeΦ (ℓ p) j)
def Umark (q:ℕ+)(G:Gauge): Beacon q G (-1) where
   seed:= μDeck q G; shade:=restU q; light p a:=single_ready (Submodule.smul_mem _ _ (degreeΦ (q:=q) (r:=-1) p a)); ridge k x f:= by rw [tune_deck]; simp_rw [map_sum,map_mul (veil x k),veil_μ,arcStone, restU,map_smul,veil_μ, ← Nat.cast_smul_eq_nsmul ℂ (2:ℕ), Nat.cast_ofNat, smul_comm (2:ℂ)] -- sdk
local notation "ι"=> (0:Tet)
lemma U_offer : Offer (Umark q G)= μLift q G:= by
    rw [μcrown]; apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl fun x _=>?_ ; change _ * ((2:ℂ) • _) = _; rw [mul_smul_comm,mul_comm (bcomp q (-1) i x)]
lemma cubic_r (f:G.ColorIndex→Curly G)(a b:U→P)(v:Hair G→₀ℂ): δ v (cubicP f a b)=cubicP ((δ v) ∘ f) a b + cubicP f ((δ v) ∘ a) b + cubicP f a ((δ v) ∘ b):= by
   unfold cubicP; simp_rw [map_sum,Derivation.map_smul, Derivation.leibniz, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; rw [← smul_add, ← smul_add]; apply congr_arg; simp only [smul_eq_mul, Function.comp_apply];ring
lemma B_offer0 : βLift q G= ∑ p:T,∑ a:U,bcomp q 1 p a*restB q p a:= by simp only [βcrown,cubic_hook]; rfl
lemma B_ridge (x:Cover)(f:Hair G→₀ℂ): δ f (veil x k (βDeck q G))= ∑ p:T,∑ a:U,treats Q f (psiF q k x 1 p a) • veil x k (restB q p a):= by
   let a(p:T)(v:U):= glyph (psiF q k x 1 p v); let b(p:T):= (δ f) ∘ a p; have hp (p:T): ∑ j:U,treats Q f (psiF q k x 1 p j) • veil x k (restB q p j)=cubicP (b p) (a (loop p)) (a (ℓ p)):= by
        rw [cubic_hook]; apply Finset.sum_congr rfl; intro i _; unfold b; rw [Function.comp_apply,show (δ f) (a p i)= C (treats Q f (psiF q k x 1 p i)) from link Q _ _, C_mul']; congr 1; unfold restB hook; simp only [map_sum,map_smul,map_mul,veil_β]; rfl
   simp_rw [hp]; rw [veils,snapβ,cubic_r,sum3]; change cubicP (b 0) (a 1) (a 2)+ cubicP (a 0) (b 1) (a 2)+ cubicP (a 0) (a 1) (b 2)=cubicP (b 0) (a 1) (a 2)+ cubicP (b 1) (a 2) (a 0)+ cubicP (b 2) (a 0) (a 1); rw [crest (a 0) (b 1) (a 2),← crest (b 2) (a 0) (a 1)]
def BMark (q:ℕ+)(G:Gauge): Beacon q G 1 where
   seed:=βDeck q G; shade:=restB q; light _ _:=single_ready (restB_s _ _); ridge k x f:= B_ridge x f
lemma B_offer : Offer (BMark q G)=βLift q G:= B_offer0.symm
end YM.PositionX.Sage
