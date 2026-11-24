import YM.MS.Halo.Madd
import YM.MS.Halo.Task
/-!
# Global color equivariance.USE actual compact basis normalization by Gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Halo
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Alps Native
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge}{n:ℕ}{b:Bool}{z:ℂ}{F H:Rack G n}{U Y:Mield G n}
local notation "S"=> field (Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product S
namespace Apple
lemma ξ : Apple (cwave n G):= pureC false _
lemma color_r (x y:Mield G n)(hx:Apple x)(he:Apple y)(z:G.El): repeatC z (sume x y)=sume x y:= by unfold sume; simp_rw [map_sum, glob_prod,hx z, he z]; exact Paint.bilateral z _ _ _
variable (a i:Arts.L n)
lemma kudzu : ShadeG (ploy G z):= by
                                       intro m k; simp only [ploy, Motif.core, map_sum,map_smul, map_add, Surf.reach,map_sub]; -- core ambiguous
                                       simp_rw [color_r _ _ (spicy _ _ ) (spicy _ _ ), color_r _ _ (pureC true _ ) ( heat _ ξ )]; rw [color_r _ _ (pureC true none) (show Apple (Sc z G m) from ((ξ.r_eq ξ).smul _))]
end Apple
lemma folk (h:ℕ): ShadeG (pulseX G h):= by
    let K:=χ G; have htag(z:ℂ): ShadeG (Literal.value (Mob G) z K):= by rw [Class_at]; intro n k; rw [Pi.sub_apply,map_sub, Apple.kudzu n k,Apple.kudzu n k]
    intro n e; funext w; let A:=Garment.Wave.slice w; let B := (LinearMap.proj w: Rack G n→ₗ[ℂ] ℂ).comp (( Color.repeatC e).comp (LinearMap.proj n: Mob G→ₗ[ℂ] Rack G n)); exact sub_eq_zero.mp (valuedZ K (B-A) (fun z=> sub_eq_zero.mpr (congr_fun (htag z n e) w )) h)
end YM.MS.Halo
