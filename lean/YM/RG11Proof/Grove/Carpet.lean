import YM.RG11Proof.Grove.Purses
import YM.RG11Proof.Scale.Grades

/-!
# Keep coefficient estimate submodules through matrix operations

Weights may depend on cluster and output, summing outputs fixed horizon
requires use `lets` with assumed geometry cost comparisons when combining
different weights. Filter and credit from Grove/Purses. This file
independent of Yang--Mills labels or regulator. Ruler in this file is c as
MS variable (but algebra general).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Grove
open PowerSeries YM.RG11.Jets Function YM.RG11.Scale
open scoped Classical BigOperators Topology
variable {I J K α : Type*}
local notation "ps"=> PowerSeries ℂ

/-- Transport both sides of a correspondence, WITH transpose convention
absorbed in R: for exteriors use R=Dᴱ^t, for output use inverse C(g). -/
def rug (p:ps)(L:Square I ps)(U:Rect I J ps)(R:Square J ps)[Fintype I][Fintype J]:Rect I J ps:= L * subs p U * R

/-- R acts on outputs: old i -> new j via R i j. So require C(u,k,v) ≤ C(u,v) for each such i for an operator preserving target cost in new output j. -/
def Affords (L: I→J→Submodule ℂ (α→ℂ))(k:ℕ)(X:α→Rect I J ps):Prop:=∀ i j n, n≤k →(fun u=>coeff n (X u i j))∈L i j

variable (W:I→J→Submodule ℂ (α→ℂ))
namespace Affords
variable {W}
 theorem roof {p:ps}(h:Anchored p){k}{X:α→Rect I J ps}(he:Affords W k X):
   Affords W k (fun u=>subs p (X u)):=by
   intro i j n hn
   simp_rw [subs_apply,coeff_compose _ _ _ h]
   let L (z:ℕ):=fun u=>coeff z (X u i j)
   rw [show (fun u=> ∑ z∈Finset.range (n+1), L z u * coeff n (p^z))= ∑ z∈Finset.range (n+1), coeff n (p^z) • L z from funext fun _=>by simp [mul_comm] ]
   exact Submodule.sum_mem _ (fun z hz=>Submodule.smul_mem _ _ (he i j z (by have ht:=Finset.mem_range.mp hz; omega)))

 theorem right [Fintype J]{k}{X:α→Rect I J ps}{R:Square J ps}
   (h:Affords W k X)(he:∀ i g j,R g j≠0→ W i g ≤ W i j): Affords W k (fun u=>X u * R):=by
   intro i j n hn
   let Y (g:J)(z:ℕ × ℕ)(u):=coeff z.1 (X u i g)
   have hv : (∑ g:J,∑ z∈Finset.HasAntidiagonal.antidiagonal n, coeff z.2 (R g j) • Y g z)∈W i j:=by
     refine Submodule.sum_mem _ (fun g _=>?_)
     by_cases hj:R g j=0
     · simp [hj]
     refine Submodule.sum_mem _ (fun z hz=> Submodule.smul_mem _ _ (he i g j hj (h i g _ ?_)))
     have ht:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz; omega
   convert! hv using 1; ext1 u; simp [Y,Matrix.mul_apply,coeff_mul,mul_comm]
 theorem left [Fintype I]{k}{X:α→Rect I J ps}{L:Square I ps}
    (h:Affords W k X)(he:∀ i g j,L i g≠0→ W g j ≤ W i j):Affords W k (fun u=>L * X u):=by
   intro i j n hn
   let Y(g:I)(z:ℕ × ℕ)(u):=coeff z.2 (X u g j)
   have hv :(∑ g:I,∑ z∈Finset.HasAntidiagonal.antidiagonal n, coeff z.1 (L i g) • Y g z)∈W i j:=by
     refine Submodule.sum_mem _ (fun g _=>?_)
     by_cases hj:L i g=0
     · simp [hj]
     refine Submodule.sum_mem _ (fun z hz=> Submodule.smul_mem _ _ (he i g j hj (h g j _ ?_)))
     have ht:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz; omega
   convert! hv using 1; ext1 u; simp [Y,Matrix.mul_apply,coeff_mul]
 theorem add {k}{X Y:α→Rect I J ps}(h:Affords W k X)(he:Affords W k Y):Affords W k (fun u=>X u+Y u):=by
   intro i j n hn; simp_rw [Matrix.add_apply,map_add]; exact Submodule.add_mem _ (h i j n hn) (he i j n hn)
 theorem replace {k}{X Y:α→Rect I J ps}(h:Affords W k X)(he:∀ u,MatThrough k (Y u) (X u)):Affords W k Y:=by
   intro i j n hn; rw [funext (fun u=>he u i j n hn)]; exact h i j n hn

end Affords

variable [Fintype I][Fintype J]
 theorem graded_season {N}{v:I→ℕ}{w:J→ℕ}{p:ps}{L:Square I ps}{R:Square J ps}(h:Anchored p)(ha:graded v L)(hb:graded w R){X:ℝ→Rect I J ps}:
   let q := fun i j=> season ((v i:ℝ)-w j)
   Affords q N X → Affords q N (fun u=> rug p L (X u) R):=by
     dsimp only; intro hq
     apply ((hq.roof h).left (fun i g j hi=>?_)).right (fun i g j hi=>?_)
     · rw [show v i=v g from not_not.mp fun he=>hi (@ha i g he)]
     rw [show w j=w g from not_not.mp fun he=>hi (@hb g j (Ne.symm he))]

-- Example penalized estimate (all shapes uniformly after threshold)
private def pcredit {Γ:Type*}(Ω : ℝ→Set Γ)(X:ℝ→Γ→ℝ)(h:Actual Ω X)(w:ℝ):Submodule ℂ (ℝ × Γ→ℂ) where
    carrier:={f| (fun u g=>f (u,g))∈credit Ω X h w}
    zero_mem':=(credit Ω X h w).zero_mem
    add_mem':=fun {a b} he hb=>(credit Ω X h w).add_mem (x:=fun u i=>a (u,i)) (y:=fun u i=>b (u,i)) he hb
    smul_mem':=fun c x hx=>(credit Ω X h w).smul_mem c (x:=fun u i=>x (u,i)) hx

def Covers {Γ:Type*}(Ω:ℝ→Set Γ)(X:ℝ→Γ→ℝ)(v:I→J→ℝ)(k:ℕ)(A:ℝ→Γ→ Rect I J ps):Prop:=
   ∀ i j n,n≤k → price Ω X (v i j) (fun u l=>coeff n (A u l i j))

 theorem graded_envelope {Γ: Type*}{Ω : ℝ→Set Γ}{X:ℝ→Γ→ℝ}(h:Actual Ω X){v:I→ℕ}{w:J→ℕ}{N}{e:ℕ→ℕ→ ℝ}{p:ps}{L:Square I ps}{R:Square J ps}(a:Anchored p)(b:graded v L)(c:graded w R){A:ℝ→Γ→Rect I J ps}
     (hA:Covers Ω X (fun i j=> e (v i) (w j)) N A):
    Covers Ω X (fun i j=> e (v i) (w j)) N (fun u t=>rug p L (A u t) R):=by
   let Q:=fun i j=>pcredit Ω X h (e (v i) (w j))
   have he:Affords Q N (fun (b:ℝ × Γ)=>A b.1 b.2):=hA
   have hz:Affords Q N (fun(b:ℝ × Γ)=>rug p L (A b.1 b.2) R):=by
     apply ((he.roof a).left (fun i g j hi=>?_)).right (fun i g j hi=>?_)
     · unfold Q; rw [show v i=v g from not_not.mp fun he=>hi (@b i g he)]
     unfold Q; rw [show w j=w g from not_not.mp fun he=>hi (@c g j (Ne.symm he))]
   intro i j n hk
   exact hz i j n hk
end YM.RG11.Grove
