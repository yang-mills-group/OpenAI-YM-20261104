import YM.FVA2.Paired
/-!
# Schur equivalence through mirror restriction on unmasked full ENSEMBLE

Use $Λ_F$,Λ_I coupled only by `Preserves/full symmetric` & `F₀=2 Λ_I P` for Quadratic.P.
Prove exact cov, update, reconstruction means. Does **not** imply identical higher
perturbative action on the two when numerically contracted (use corrected Wick rule).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Mirror
open Function Filter Topology MeasureTheory PertExtension Precision
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Papers
open PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial GaussianScore PowerSeries
open MeasureTheory.Measure (IsAddHaarMeasure)
open scoped Topology ContDiff BigOperators Classical
variable {E F U K : Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup U][NormedAddCommGroup K][NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ U][NormedSpace ℝ K]
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F][FiniteDimensional ℝ U][FiniteDimensional ℝ K]

structure House (X Y:Type)[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ X][NormedSpace ℝ Y] where
   t : Module.End ℝ X
   inv(x:X): t (t x)=x
   ε : Y→ₗ[ℝ] X
   assess (y:Y) : t (ε y)=ε y
   π:X→ₗ[ℝ] Y
   lift (x:X) : t x=x→ε (π x)=x
   recovery (y:Y): π ( ε y )=y

namespace House
variable (A:House E U)(B:House F K)
def join : House (E×F) (U×K) := {
 t:= A.t.prodMap B.t
 inv:= fun x=>Prod.ext ( A.inv _ ) (B.inv _ )
 ε := A.ε.prodMap B.ε
 π := A.π.prodMap B.π
 assess:= fun x=> Prod.ext ( A.assess _ ) ( B.assess _ )
 lift := fun x h=> Prod.ext ( A.lift _ (congr_arg Prod.fst h) ) ( B.lift _ (congr_arg Prod.snd h) )
 recovery:= fun x=>Prod.ext ( A.recovery _ ) (B.recovery _) }
lemma εinj : Injective A.ε:= fun p q h=> by rw [ ← A.recovery p,← A.recovery q,h]
end House
variable (H:House E U) (T:House F K)
abbrev invariant (H:House E U)(V:Quadratic E): Prop:= ∀ x y:E,V.P ( H.t x ) ( H.t y ) = V.P x y
-- full vs inversion primitive. no Precious.Native hypotheses hidden.
structure Related (H:House E U)(V:Quadratic E)(W:Quadratic U): Prop where
   living : invariant H V
   weight (x y:U): V.P ( H.ε x ) ( H.ε y ) = 2* W.P x y
set_option quotPrecheck false
namespace Related
variable (V:Quadratic ( E × F )) (W:Quadratic (U × K)) (hr: Related ( H.join T ) V W)
local notation "T₀"=> H.join T
local notation "Δf"=> Quadratic.core V
local notation "Δi"=> Quadratic.core W
include hr
lemma held : Related H ( Quadratic.core V ) ( Quadratic.core W ) := by
     constructor
     · intro x y; change V.P (H.t x,0) (H.t y,0)=V.P (x,0) (y,0); nth_rw 1 [←map_zero T.t]; nth_rw 2 [←map_zero T.t]; exact hr.living (x,0) (y,0)
     intro x y; change V.P (H.ε x,0) (H.ε y,0)=_; nth_rw 1 [← map_zero T.ε]; -- second target indices due Zero used in map.Zero changes.Hf
     rw [show ( H.ε x,T.ε 0 )= (T₀).ε (x,0) from rfl,show (H.ε y, (0:F))= (T₀).ε (y,0) from Prod.ext rfl (map_zero T.ε).symm]; exact hr.weight ..

variable (h:V.core.RespectsPrice)(g:W.core.RespectsPrice)
local notation "Ω" => V.skew h
local notation "Θ" => W.skew g
include h
lemma legal_t (x y:E)(b c:F): V.P (H.t x,T.t b) (H.t y,T.t c)= V.P (x,b) (y,c):= hr.living (x,b) (y,c)
lemma mirror_m (p:F): H.t (Ω p)= Ω ( T.t p ):= Tandem.optimize.only V h _ _ (fun x=> by
     rw [ ← H.inv x, show (H.t ( H.t x ),(0:F))=(H.t (H.t x),T.t 0) from Prod.ext rfl (map_zero _).symm, Related.legal_t H T V W hr h ]; exact RayScatter.square.cross_zero V h p ( H.t x ))
include g
lemma inter (u v:U)(b c:K): V.P ( H.ε u, T.ε b ) (H.ε v,T.ε c)=2*W.P (u,b) (v,c):= hr.weight (u,b) (v,c)
lemma η_mean (p:K): Ω ( T.ε p )= H.ε ( Θ p ) := by
    let u:= T.ε p; let v:= Ω u; have hu: H.t v=v:= by unfold v u; rw [ mirror_m H T V W hr,T.assess ]; -- expects arguments h implicit explicit
    let L:= H.π v; have hL: H.ε L=v:= H.lift v hu
    have he : L=Θ p:= Tandem.optimize.only W g _ _ (fun x=> by have hv := inter H T V W hr h g L x p 0; rw [map_zero,hL] at hv; rw [show V.P ( v, _ ) _=0 from RayScatter.square.cross_zero V h u ( H.ε x )] at hv; linarith
                                                            ) -- simp orientation
    rw [ ←he, hL ]; -- rfl

lemma earth : Related T (V.reduced h) (W.reduced g):= by
     constructor
     · intro p q; change V.P (Ω _, _) (Ω _,_)= _; change V.P (Ω (T.t p),T.t p) (Ω (T.t q),T.t q)=V.P (Ω p,p) (Ω q,q); rw [← mirror_m H T V W hr,← mirror_m H T V W hr,legal_t H T V W hr h]
     intro p q; change V.P (Ω _, _) (Ω _,_)= _; change V.P (Ω (T.ε p),T.ε p) (Ω ( T.ε q ),T.ε q)=_; rw [η_mean H T V W hr h g,η_mean H T V W hr h g]; exact inter H T V W hr h g _ _ _ _
end Related
-- Mirrors on arbitrary finite real positive forms. Cull metric. inverse formula arbitrary modes.
section Wick
variable (S:Law E)(Q:Law U)(H:House E U)(h:Related H (Quadratic.recordQ S) (Quadratic.recordQ Q))
include h
abbrev Θ (ℓ:Module.Dual ℝ E): Module.Dual ℝ U:=ℓ ∘ₗ H.ε -- variable only H actually syntax
lemma actions_in (p q:E): S.P (H.t p) (H.t q)= S.P p q:= h.living p q
lemma prices_out (p q:U): S.P (H.ε p) (H.ε q)=2* Q.P p q:= h.weight p q
variable (ℓ k: Module.Dual ℝ E)
lemma inverse_flip : S.inverse (ℓ∘ₗ H.t)= H.t (S.inverse ℓ):= by
     suffices hv:S.P (H.t (S.inverse ℓ))= (ℓ∘ₗ H.t) by rw [←hv, Law.solves]
     apply LinearMap.ext; intro x; rw (occs:=.pos [1]) [ ← H.inv x ]; rw [ actions_in S Q H h,Law.applies ]; rfl
lemma inverse_odd : H.ε (Q.inverse (ℓ∘ₗ H.ε))= S.inverse ℓ + H.t (S.inverse ℓ) := by
     let x:= S.inverse ℓ; let y:= x + H.t x; have ht:H.t y=y:= by unfold y; rw [map_add,H.inv,add_comm]
     let v:= H.π y; have hv : H.ε v=y:= H.lift y ht; suffices he: Q.P v= (ℓ∘ₗ H.ε) by rw [ ←he,Q.solves,hv ];
     apply LinearMap.ext; intro i; obtain hi:= prices_out S Q H h v i; rw [hv] at hi; unfold y at hi; rw [map_add,LinearMap.add_apply,show S.P ( H.t x ) (H.ε i)=S.P x (H.ε i) from ?_, show S.P x= _ from Law.applies S ℓ] at hi; change _= ℓ (H.ε i); linarith
     nth_rw 1 [← H.assess i]; rw [actions_in S Q H h]
/-- Exact Cov full+image in the prescribed gauge. No averaging factor; action was halved.
 Sign automatically on the reflected test functional.
 -/
theorem images_wick : Q.wick (ℓ ∘ₗ H.ε) (k∘ₗ H.ε)= S.wick ℓ k + S.wick ℓ (k∘ₗ H.t):= by unfold Law.wick; rw [LinearMap.comp_apply, inverse_odd S Q H h ℓ,map_add ]; rfl
end Wick
end YM.FVA2.Mirror
