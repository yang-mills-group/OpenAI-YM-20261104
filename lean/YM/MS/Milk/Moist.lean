import YM.MS.Milk.Pure
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
open Puff
variable {L:Album X G}{u:X} {y:ℝ}{Q:Normal.Symmetric X}
lemma upper0 (i:X): Limit ( L.H i ) 1:= fun l hl=> L.line i l (by rw [mod_int]; omega)
lemma already0 (i:X): deep G s ( L.H i )=0:= by rw [ weightC ( L.cost i ).1 ]; funext w; exact (Latch.capcy ( upper0 i ) (Rake.PlanetD G s) Osc.Snap.planeF) w (by omega)
abbrev Δcontact (L:Album X G)(i j:X)(s:ℝ): ℂ:= ( Move G s ).join ( L.H i ) ( L.H j ) []
lemma sic (F:X) : linkD G y ( L.H u ) ( L.H F )= coin (Δcontact L u F y):= by
   let Z(v:X):= L.H v; funext l; rcases l with _|⟨j,l⟩; rfl; rw [ oriented ( L.cost u ).1 ( L.cost F ).1 ]; exact capjoin ( upper0 u ) ( upper0 F ) _ _ _ _ (by simp)
lemma wetted (p:Normal.poly X)(s:ℝ)(i:X): linkD G s (L.H i) (bowl L p)=bowl L (slit (fun j=> Δcontact L i j s) p):= by
   induction p using MvPolynomial.induction_on with
   | C a=> rw [show (MvPolynomial.C a:Normal.poly X)=a • (1:Normal.poly X) from ( by rw [← MvPolynomial.C_mul',mul_one] ),map_smul,(slit (fun j=> Δcontact L i j s)).map_smul,t_1,map_smul,show linkD G s (L.H i) (coin 1)=0 from Engine.simple (Move G s) ( L.cost i ), ( slit _ ).map_one_eq_zero,smul_zero,smul_zero,map_zero ]
   | add p q hp hq=> simp only [map_add,hp,hq]
   | mul_X q x ih=> rw [mul_comm q,t_M,t_X,whisperD _ ( L.cost i ) (L.cost x) (roof_v L q),sic,ih,slit_prod ,map_add,t_M,t_M,t_X,t_C,add_comm ]
lemma drenched (p:Normal.poly X)(s:ℝ)(i:X) : linkD G s (L.H i) (Tint L Q p) = Tint L Q ( slit (fun j=> Δcontact L i j s) p):= by unfold Tint; rw [LinearMap.comp_apply,wetted,skims ]; rfl
lemma cost' [DecidableEq A](i: A→X)(a:Finset A): Limit ( Tint L Q (glyphs i a) ) a.card:= by
   induction a using Finset.strongInduction with
   | H v ih=>
      obtain hx|hx:= v.eq_empty_or_nonempty; · subst v; rw [Normal.glyphs,Finset.prod_empty,step0,Finset.card_empty]; exact fun l hl=>by cases l; simp at hl; rfl
      obtain ⟨k,hk⟩:= hx; let T:= v.erase k; have hv:= Finset.erase_ssubset hk; have hW:T.card+1=v.card:= Finset.card_erase_add_one hk; rw [ ← insert_erase hk ]; rw [step_k L i ( Finset.notMem_erase k v ), insert_erase hk, ← hW ]; push_cast; refine Limit.add ?_ ?_ -- signature
      · rw [add_comm _ 1]; exact ( upper0 ( i k ) ).pair (ih T hv)
      refine Limit.sum _ (fun j hj=> Limit.up ( Limit.smul _ ( ih _ ( Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) hv )) ) ?_ ); have ht : ( T.erase j ).card≤ T.card := Finset.card_le_card ( Finset.erase_subset .. ); dsimp only [T] at *; omega
variable [DecidableEq A]{t:ℝ→ Normal.Symmetric X}
structure Standard (L:Album X G)(t:ℝ→Normal.Symmetric X): Prop where
   voice (i j:X)(s:ℝ): HasDerivAt (fun r:ℝ=> ( t r ).cov i j) ( Δcontact L i j s ) s
-- derivative.CCY. EP.Engine
lemma rune (F:OM (Lane4 G))(c:ℝ→ℂ)(x:ℝ){H:Law G}(hp:Lead F H x){T:ℂ}(ht: HasDerivAt c T x): Lead (fun i=> c i • F i) ( c x • H + T • F x ) x:= by intro l; obtain he:= ht.mul ( hp l ); rw [ add_comm (T*_) ] at he; exact he
lemma sail_k (h:Standard L t)(u:A→X)(a:Finset A) (j:ℝ): Lead (fun s=> Tint L ( t s ) ( glyphs u a ) ) ( deep G j ( Tint L ( t j ) (glyphs u a) ) ) j:= by
    let T(v:Finset A)(s:ℝ):= Tint L (t s) (glyphs u v); induction a using Finset.strongInduction with
    | H a ih=>
       obtain hv|hv:= a.eq_empty_or_nonempty; · subst a; simp only [Normal.glyphs, Finset.prod_empty,step0, show deep G j (coin 1)=0 from ( Move G j ).unitLaw ]; exact fun l=> hasDerivAt_const ..
       obtain ⟨i,hp⟩:=hv; let v:=a.erase i; have ht : v ⊂ a:= erase_ssubset hp; let f:= L.H (u i); have he:= L.cost (u i); let P( k:A )(x:ℝ):= ( t x ).cov ( u i ) (u k); let V:= Δcontact L (u i)
       rw [ ← insert_erase hp ]; simp_rw [step_k L u ( Finset.notMem_erase i a )];
       have hA(t:X)(F:Law G)(hf:F∈Roof G): deep G j ( L.H t ⋆ F )= (deep G j (L.H t) ⋆ F )+(L.H t ⋆ deep G j F)+ linkD G j (L.H t) F:= ( Move G j ).compatibility _ _ ( L.cost t ) hf
       rw [map_add,hA _ _ (fills L _), already0, map_zero, LinearMap.zero_apply,zero_add,drenched, renew (fun k=> Δcontact L (u i) k j) u v,map_sum,map_sum ]; 
       simp_rw [map_smul]; rw [add_assoc]; unfold v; rw [ add_comm (∑ i∈a.erase _,( (Δcontact L (u _ ) (u i) j) • _ : Law G )) ( ∑ _i∈a.erase _,_ ), ← Finset.sum_add_distrib ]; intro w; simp_rw [ Pi.add_apply, Finset.sum_apply ]; apply HasDerivAt.add; · obtain he:= HeatFlow.lead_pair (p:=Φκ) (F:=fun _=> L.H (u i)) (H:=T v) (t:=j) (f:=0) ( fun i=>hasDerivAt_const .. ) ( ih v ht ); rw [ map_zero,LinearMap.zero_apply, zero_add ] at he; exact he w
       exact HasDerivAt.fun_sum (fun k _=> rune (T (v.erase k)) ( P k ) j ( ih _ ( Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) ht ) ) ( h.voice _ _ j ) w)
omit [DecidableEq A]
abbrev arc (p:Normal.poly X)(L:Album X G)(U:ℝ→Normal.Symmetric X)(s:ℝ):= Tint L (U s) p
lemma Lift (h:Standard L t)(p:Normal.poly X): Status ( arc p L t ) (fun s=> deep G s (arc p L t s)):= by
   classical
   let Φ: Normal.poly X→ₗ[ℂ] OM ( Lane4 G ):= LinearMap.pi ( fun s=> Tint L ( t s ) ); let M : Normal.poly X→ₗ[ℂ] OM ( Lane4 G ):= ( varied ℝ fun s=> deep G s ) ∘ₗ Φ; let S:Submodule ℂ (Normal.poly X):={ carrier:=setOf fun p=> Status (Φ p) (M p), zero_mem':= by simp only [ mem_setOf_eq,map_zero ]; exact status_0 _, smul_mem':= fun x p h=> by simp only [ mem_setOf_eq, map_smul ]; exact status_cast h x, add_mem' := fun h hA=> by simp only [ mem_setOf_eq,map_add ]; exact status_plus h hA }; exact (show p∈ S from axis_v S (fun a=> show Status (arc (Gaze a) L t) _ from ⟨ ⟨a.card,fun v=> cost' Prod.snd a⟩ ,fun _=>sail_k h Prod.snd a _⟩ ) p)
end YM.MS.Milk
