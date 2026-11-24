import YM.MS.Rock.Claim
import YM.MS.Rock.StarRy
/-!
# Holomorphic class of param ext, line and taper.

Doesn't prescribe Taylor valuation, support. Uniform radius disk with constants per
 test chart in auxiliary Euclidean. Scalar holomorphic condition suffices by proof
 House. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I E F H J:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 {m n k:ℕ}{z:UScale I}{a b : I→ℝ}{r:ℝ}{f g:ℂ→Mob G} {u:ℂ→ Rip G}
variable {D:Set ℂ}
structure Hop (D:Set ℂ)(u:ℂ→ Rip G): Prop where
   price c R:0<R→ closedBall c R⊆D→ rib 0 (fun _:closedBall c R=>1) (fun i=>u i)
   top m a b p: Forest D fun z=> u z m a b p
namespace Path
-- scalar hol of wing
lemma wing_rays (H:Hol D f)(h: Hop D u)(W:Touch G m E): keys D (fun i=>wing i (u i) (f i) W):= by
   intro x z hz; let s:= Nat.lt_succ_self m; unfold wing Wtr; simp only [Pi.add_apply,at_trc,Pi.smul_apply]; refine DifferentiableAt.add (DifferentiableAt.fun_sum fun i _=> DifferentiableAt.fun_sum fun j _ => (h.top _ _ _ _ z hz).mul (H.top _ _ z hz)) ?_ ; refine (show DifferentiableAt ℂ (fun i:ℂ=> 2*(i-(m+1:ℕ))) z from by fun_prop).smul ?_; unfold yeast; exact DifferentiableAt.fun_sum (fun i _ => DifferentiableAt.fun_sum (fun j _=> DifferentiableAt.fun_sum fun k _=> DifferentiableAt.fun_sum (fun c _=> (h.top _ _ _ _ _ hz).mul (H.top _ _ _ hz))))
lemma price_const (n:ℕ)(c:ℂ)(R:ℝ): scaleC 0 1 fun i:closedBall c R=> ‖(2*(i.val-(n:ℂ)):ℂ)‖:= by
    let f (z:ℂ):=‖2*(z-n)‖; obtain ⟨C,hC⟩:= ((isCompact_closedBall c R).image (f:=f) (by unfold f; fun_prop)).bddAbove; refine ⟨max C 1,lt_max_of_lt_right zero_lt_one,0,fun i p _=>?_⟩; simpa only [pow_zero,mul_one,Pi.one_apply] using le_trans (hC (mem_image_of_mem _ i.property)) (le_max_left C 1)
lemma wind_he (H:Hol D f)(h: Hop D u)(hD:D⊆ Town){b:Bool}(hm:∀ i∈D,Sturdy b (f i))(hh:∀ i∈D,Ruddy b (u i))(hk:IsOpen D): Hol D fun i=> ocean i (u i) (f i) where
    price c R hr hp := by
        obtain ⟨m,hQ⟩:= mag c R; convert! regular_fin (Z:=fun i:closedBall c R=>i.val) (fun i=> price_const i _ _) (H.price c R hr hp) (h.price c R hr hp) (fun i=>hD (hp i.property)) (fun i=>hQ _ i.property) (fun i=>hm _ (hp i.property)) (fun i=>hh _ (hp i.property)) (fun _=>zero_le_one) using 1; simp
    top := by
        intro m l; let U(z:ℂ):= wing z (u z) (f z) (ray l); have Hx : Arc.Tracks D U:= ⟨fun c R hr ht=> by convert (sky (Z:=fun i=>i.val) (fun i=>price_const i _ _) (H.price c R hr ht) (h.price c R hr ht) (fun _=> zero_le_one) (ray l)) using 1; funext i; simp, wing_rays H h _⟩; exact ( Arc.Tracks.p (Px m) Hx hk (fun i hi=> wing_mirror (hm i hi) (hh i hi) _ _) hD m).root 1 -- spout
end Path
end YM.MS.Rock
