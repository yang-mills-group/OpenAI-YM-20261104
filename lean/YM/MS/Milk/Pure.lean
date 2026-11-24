import YM.MS.Drops.Catch
import YM.Next.RANK.GaussLeg
import YM.MS.Awning.Press
/-!
# Free Wilsonian solution ($MS physics$) in coordinate kernel.Design any actual alphabet
 and full cost constraints. Use signed Wick polynomial operations (Next.RANK.NORMAL).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell
open Tensor (diagonal)
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X:Type}{G:Gauge}{n d r:ℕ}{s:ℝ}{f:Local.BV.Grade G}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
abbrev deck0 (Y:Type):= ℕ×Y
abbrev Gaze (s:Finset (deck0 X)):= glyphs Prod.snd s
lemma fresh0 (s:Finset (deck0 X))(x:X): ∃ n:ℕ,(n,x)∉ s:= by
   classical
   let n:= s.sup Prod.fst; refine ⟨ n+1,fun h=>?_⟩; obtain he:n+1≤ n:= Finset.le_sup (f:=Prod.fst) h; omega
open MvPolynomial (X)
lemma axis_v (V:Submodule ℂ ( Normal.poly X ))(h:∀ s:Finset (deck0 X),Gaze s∈V)(p:Normal.poly X) : p∈ V:= by
    classical
    let S:Submodule ℂ ( Normal.poly X ):= Submodule.span ℂ ( Set.range Gaze ); refine (show S ≤ V from Submodule.span_le.mpr (by rintro _ ⟨s,rfl⟩; exact h s) ) ?_; -- Lean X shadow.
    have hp(s:Finset (deck0 X)): Gaze s∈ S:= Submodule.subset_span (Set.mem_range_self s); induction p using MvPolynomial.induction_on with
    | C a=> rw [show ( MvPolynomial.C a: Normal.poly X )= a • Gaze ( ∅:Finset ( deck0 X ) ) from (by unfold Gaze Normal.glyphs; rw [Finset.prod_empty,← MvPolynomial.C_mul',mul_one] )]; exact smul_mem _ _ (hp _)
    | add p q hx hv=>exact S.add_mem hx hv
    | mul_X q x ih=>
        apply ( show S ≤ Submodule.comap ( LinearMap.mulRight ℂ ( MvPolynomial.X x ) ) S from ?_ ) ih; rw [Submodule.span_le]; rintro _ ⟨s,rfl⟩; obtain ⟨i,hi⟩:= fresh0 s x; change Gaze s* MvPolynomial.X x∈ S; obtain he:= hp (insert ( i,x ) s); rw [mul_comm]; rw [ Gaze,Normal.glyphs,Finset.prod_insert hi ] at he; exact he
-- Blueprint.F defeats ∀. Strictly rank1 and Even.
structure Album (X:Type)(G:Gauge) where
    H:X→ Law G
    cost i: H i∈Roof G
    line i : Book.rank 1 ( H i )
variable (L:Album X G) {b:ℕ}{Q:Normal.Symmetric X}
abbrev sight (i:X): ↥( Theater.Dark Φκ ):= ⟨ L.H i,( L.cost i ).2 ⟩
def tintK (L:Album X G): Normal.poly X→ₐ[ℂ] ↥( Theater.Dark Φκ ):= MvPolynomial.aeval (sight L)
def bowl (L:Album X G): Normal.poly X→ₗ[ℂ] Law G:= ( Theater.Dark Φκ ).subtype ∘ₗ ( tintK L ).toLinearMap
lemma t_X (i:X): bowl L (MvPolynomial.X i)= L.H i:= congr_arg Subtype.val (MvPolynomial.aeval_X ( sight L ) i)
lemma t_C (i:ℂ): bowl L (MvPolynomial.C i)= coin i:= by unfold bowl tintK; simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply, MvPolynomial.aeval_C,coe_subtype ]; exact cash1 .. -- Wall
lemma t_1 : bowl L 1=coin 1:= by rw [← (map_one (MvPolynomial.C (R:=ℂ) (σ:=X))), t_C L]; -- C namespace R
lemma t_M (p q:Normal.poly X): bowl L (p*q)= bowl L p ⋆ bowl L q:= by unfold bowl; rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply,map_mul ]; rfl -- field
lemma roof_v (p:Normal.poly X): bowl L p ∈ Roof G:= by
   induction p using MvPolynomial.induction_on with
   | C c=> rw [show ( MvPolynomial.C c:Normal.poly X )= c • 1 from (by rw [ ← MvPolynomial.C_mul',mul_one ] ),map_smul,t_1 L ]; exact ( Roof G ).smul_mem c Roof.unit
   | add p q hp hv=> rw [map_add]; exact ( Roof G ).add_mem hp hv
   | mul_X q x h=> rw [t_M L,t_X L]; exact Roof.core h (L.cost x)
abbrev Tint (Q:Normal.Symmetric X): Normal.poly X →ₗ[ℂ] Law G:= bowl L ∘ₗ milk Q
lemma fills (p:Normal.poly X): Tint L Q p∈Roof G:= roof_v L _
-- `feeds` recurrence.
lemma tints (u: X)(p:Normal.poly X): Tint L Q ( MvPolynomial.X u * p ) = L.H u ⋆ Tint L Q p + Tint L Q ((slit ( Q.cov u )) p):= by unfold Tint; rw [LinearMap.comp_apply, feeds, skims,map_add, t_M,t_X ]; rfl
lemma step_k [DecidableEq A]{s:Finset A}{u:A}(R:A→X)(h:u∉s): Tint L Q (glyphs R ( insert u s ))= L.H (R u) ⋆ Tint L Q (glyphs R s)+ ∑ i∈s, Q.cov (R u) (R i) • Tint L Q (glyphs R (s.erase i)) := by
    unfold Normal.glyphs; rw [Finset.prod_insert h, tints (Q:=Q) ]; refine congr_arg ( L.H (R u) ⋆ Tint L Q (glyphs R s) + · ) ?_; rw [renew ( Q.cov ( R u ) ) R s,map_sum ]; simp_rw [map_smul]; -- need changes
lemma cash0 (c:ℂ): Tint L Q (MvPolynomial.C c)=coin c:= by unfold Tint; rw [LinearMap.comp_apply, fine,t_C]
lemma step0 : Tint L Q 1=coin 1:= by unfold Tint; rw [LinearMap.comp_apply,Normal.pure,t_1]
end YM.MS.Milk
