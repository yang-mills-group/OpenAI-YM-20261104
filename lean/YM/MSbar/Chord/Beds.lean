import YM.MSbar.Wave.Cola
import YM.Push.STRESS_FLUX.Orbits
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform Matrix
open Precision Exterior Gauge MSbar.Wave MSbar.Cacao StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}
local notation "X"=> Positions (Primary n G)
local notation "S'"=> Site n
local notation "A"=>Edge (Site n)
abbrev FaceRail (n:Side)(G:Gauge):=Positions (Primary n G) →L[ℝ] Positions (Primary n G)→L[ℝ]ℝ
variable (Q:FaceRail n G)
structure Ribbon (Q:FaceRail n G): Prop where
    color (k:G.El)(x y:X): Q (hue k x) (hue k y)=Q x y
    axial (k:Signed)(b:S')(x y:X): Q (bandE k b x) (bandE k b y)=Q x y
    zeroG (t:Site n→G.Color)(x:X) : Q x (grad t)=0
include Q
lemma Ribbon.negative (h:Ribbon Q): Ribbon (-Q) := by
    refine ⟨fun k x y=>?_,fun k b x y=>?_,fun k x=>?_⟩; rw [_root_.neg_apply,_root_.neg_apply,h.color]; rfl; rw [_root_.neg_apply,_root_.neg_apply,h.axial];rfl; rw [_root_.neg_apply,_root_.neg_apply,h.zeroG,neg_zero] -- tactics
lemma ribbon (F:Nesting G n) (R:PathData G)(p:Clip)(u:ℕ)(i:ℕ){S:ℝ → Config G n → ℝ} (h:Trend S F R p u)(hG:G.Simple)(hi:i≤u)(he:Q=rim (joy (tariff n u p R F) i)): Ribbon Q:=by
    subst Q; let f:= joy (tariff n u p R F) i; have hh(k:G.El): f ∘ hue k=ᶠ[𝓝 0] f:= Eventually.of_forall (fun x=> inh R p F u h i hi k x); have hf:ContDiffAt ℝ 2 f 0:= (vent ..).contDiffAt.of_le le_top
    have hp:=zero_hit hf hG hh; exact ⟨fun k => classR (hh k) hf hp,fun s b=>classR (Eventually.of_forall (fun i'=> ins R p F u h i hi s b i')) hf hp,gentle R p F u h i hi hG⟩
def cell (e v:Edge (Site n)) (x y:G.Color) := Q (bead G e x) (bead G v y)
local notation "ϕ"=> cell Q
local notation "ω'"=> (bead G)
variable {p:ℕ}
omit Q in
lemma gradient_shift (e:A)(b:S')(s:Signed)(x:G.Color) : bandE s b (bead G (sendEdge s b e) x) = sign s e.2 • bead G e x:=by
    let Y:=panel G n; have hp:panel G n (bandE s b (bead G (sendEdge s b e) x))=pullDir s b (panel G n (bead G _ x)):= (panel G n).apply_symm_apply _; apply (panel G n).injective; rw [hp, map_smul,edges,edges]; funext i
    change sign s i.2 • (Pi.single (sendEdge s b e) x: Directions G n) (sendEdge s b i)= sign s e.2 • (Pi.single e x:Directions G n) i; by_cases he:i=e; rw [he,Pi.single_eq_same,Pi.single_eq_same]; rw [Pi.single_eq_of_ne (sendEdge_injective s b|>.ne he),Pi.single_eq_of_ne he]; simp
variable (hG:G.Simple)(h:Ribbon Q)
include h hG
lemma blazing (e v:A) (i:G.Color)(hi:‖i‖=1) (x y:G.Color): ϕ e v x y=ϕ e v i i *inner ℝ x y:=by
    let F:G.Color→ₗ[ℝ]G.Color→ₗ[ℝ]ℝ:={
        toFun:=fun x=> (Q (bead G e x)).toLinearMap.comp (bead G v).toLinearMap
        map_add' x y:=by ext1 z; change Q (bead _ _ (_+_)) _=_; rw [map_add,map_add,_root_.add_apply]; rfl
        map_smul' r x:=by ext1 z; change Q (bead _ _ (r •x)) _=_; rw [map_smul,map_smul,_root_.smul_apply]; rfl }
    obtain ⟨c,hc⟩:= StressFlux.bilinear_real hG F (StressFlux.bilinear_infinitesimal F (fun v' a b=>by
        change Q (bead G e (G.adjoint v' _)) (bead G v (G.adjoint v' _))=_; rw [shadeK,shadeK,h.color];rfl)); change F x y= F i i*_; rw [hc,hc,real_inner_self_eq_norm_sq,hi,one_pow,mul_one]
omit hG
lemma flips (e v:A)(s:Signed)(t:Site n)(x y:G.Color) : ϕ (sendEdge s t e) (sendEdge s t v) x y = sign s e.2 * sign s v.2*ϕ e v x y :=by
   unfold cell; rw [←h.axial s t (bead G _ x) (bead G _ y),gradient_shift,gradient_shift,map_smul,map_smul]; simp; ring -- smul errors
omit Q h in
lemma brand (e:A)(c:G.ColorIndex): bead G e (EuclideanSpace.basisFun G.ColorIndex ℝ c)=bolt (primary e c) :=by
    let i:=primary e c; apply (panel G n).injective; rw [edges]; funext x; ext k; change ((Pi.single e _:Directions G n) x) k= (bolt i) ((x.1,Exterior.coord x.2),k); by_cases he:x=e
    · rw [he,Pi.single_eq_same]; unfold i primary; by_cases h:k=c
      · rw [h]; simp [bolt]
      simp [bolt,h,Ne.symm h]; -- [EuclideanSpace.basisFun_apply,Pi.single_apply,h,Ne.symm h]
    have hv: primary x k≠ i:= by intro hg; have h:(x.1,Exterior.coord x.2)=(e.1,Exterior.coord e.2):= congr_arg Prod.fst hg; exact he (Prod.ext (Prod.mk.inj h|>.1) (axisEquiv.injective (Prod.mk.inj h|>.2)))
    change _=bolt i (primary x k); rw [show bolt i (primary x k)=(0:ℝ) from (by simp [bolt,hv]),Pi.single_eq_of_ne he]; rfl
end YM.MSbar.Midpoint
