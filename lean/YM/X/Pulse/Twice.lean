import YM.X.Pulse.Part
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
open Pert.Position Maxwell Maxwell.Free Bare Function Pert.RawLabels
variable {F:Labels.Frames G}(S:Bare.Shop F) (w:Floor R)
local notation "E"=> Pert.Position.E F
local notation "A"=> F.level d
local notation "L"=> Labels.Label G d
local notation "E₀"=> epsilon q k
variable (Y:T→ℕ)
open Finset
variable {e:ℝ}(P:Fin k→Word G)
variable {j m:ℕ}(x:Fin m→ Site n)
local notation "Z"=> poly (Jam n G)
section cov
variable (b:Fin m→ℕ)(t:ℝ)(z:poly (Jam n G))(p:Fin m → Labels.Label G d)(u:Signed)
def tune (t:ℝ)(d:ℕ)(b:Fin m→ℕ)(z:poly (Jam n G)):= chapters (d:=d) (fun i=> sales (d:=d) S (b i) t (x i)) z
lemma hour_tune (v:ℝ): hours S x v z d=tune S x v d 0 z:=rfl
abbrev queue (i:Fin m):Fin m→ℕ:= Function.update (fun _=>0) i 1
lemma tune_b : first_b S x t d=(∑ i:Fin m,tune S x t d (queue i) 1)-tune S x t d 0 (gas G n):= by
    unfold first_b; apply congr_arg (fun a=>a-hours S x t (gas G n) d); apply Finset.sum_congr rfl; intro j _; unfold tune; apply congr_arg (chapters · 1); funext i; by_cases hv:i=j<;>simp [hv,queue]
lemma sales_star(t:ℝ)(z:Site n)(u:Labels.Label G d): sales S k t z (Labels.realBar u)= retro (Jam n G) (sales S k t z u):= by
    rw [← (F.level d).basis.sum_repr u,map_sum,map_sum,map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smulₛₗ,map_smul,map_smul,retro_scale,(F.level d).realForm i, symbols,retro_hair]; unfold mint; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),retro_scale,retro_book]; simp
lemma tune_star (h:retro (Jam n G) z=z): tune S x t d b z (Labels.realBar ∘ p)=star (tune S x t d b z p) := by
    unfold tune; simp_rw [chapter_val,Function.comp_apply,sales_star,←map_prod]; rw [← shock_retro sale (fun i j:Jam n G=> by simp [sale])]; rw [map_mul (retro (Jam n G)),h]
lemma sales_signed(t:ℝ)(p: Labels.Label G d)(z:Site n): sales S k t (u.act z) (Labels.tensor u.ortho p)=Dial.relay u (sales S k t z p):= by unfold sales; simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,← Dial.proposed,← held_spin] -- potential simp loop
lemma tune_signed : tune S (u.act ∘ x) t d b (Dial.relay u z) (Labels.tensor u.ortho ∘ p)=tune S x t d b z p:= by unfold tune; simp_rw [chapter_val,Function.comp_apply,sales_signed,← map_prod, ← map_mul,whir]
local notation "U"=> Pert.Rigid.wear F d
set_option quotPrecheck false
local notation "g"=> (Model F).conj (hierarchy F).spin d
lemma part_signed (f:Fin m→ E d): partM S n t (u.act ∘ x) d k ((U u) ∘ f)=partM S n t x d k f:= by
    have hx: physicalLabel F d ∘ (U u ∘ f)= Labels.tensor u.ortho ∘ (physicalLabel F d ∘ f):= by funext i; rw [Function.comp_apply,Function.comp_apply, Pert.Rigid.wear_ride];exact physical_ortho ..
    by_cases ht:k=0
    · rw [ht,coins_view,coins_view,hour_tune,hour_tune,hx]; simpa only [map_one] using! tune_signed S x 0 t 1 (physicalLabel F d ∘ f) u -- fix
    have he (n:Side)(x:Fin m→ Site n):partM S n t x d k=partM S n t x d 1:= by unfold partM; rw [if_neg ht, if_neg Nat.one_ne_zero]
    let k':=physicalLabel F d ∘ f;rw [he n _,he n _,bill₁_view,bill₁_view,tune_b,tune_b,hx]; simp only [MultilinearMap.sub_apply,MultilinearMap.sum_apply]; exact congr_arg₂ (·-·) (Finset.sum_congr rfl (fun i _=> by simpa only [map_one] using! tune_signed S x (queue i) t 1 k' u)) (by simpa only [prop_gas] using! (tune_signed S x 0 t (gas G n) k' u))
lemma part_star (f:Fin m→ E d): partM S n t x d k (g ∘ f)=star (partM S n t x d k f):= by
    let k':= physicalLabel F d ∘ f; have hp: physicalLabel F d ∘ (g ∘ f) = Labels.realBar ∘ k':= by ext1 i; exact physical_real F (f i) _
    by_cases ht:k=0; · rw [ht,coins_view,coins_view,hp,hour_tune]; exact tune_star S x 0 t 1 k' (map_one _)
    rw [show partM S n t x d k=partM S n t x d 1 from (by unfold partM; rw [if_neg ht,if_neg Nat.one_ne_zero]),bill₁_view,bill₁_view,tune_b,hp]; simp only [MultilinearMap.sub_apply,MultilinearMap.sum_apply,star_sub,star_sum]; exact congr_arg₂ (·-·) (Finset.sum_congr rfl fun i _=> tune_star S x _ t 1 k' (map_one _)) (tune_star S x _ t (gas G n) k' retro_gas)
end cov
end YM.PositionX.Pulse
