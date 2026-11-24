import YM.MS.Port.Cloud
/-!
# Anchored port. μ=plane. No convergence penalty.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Port
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo Vane
open Osc Fiddle Snap Book.Convolve Alps Arts City
open scoped Topology ContDiff Interval
variable { G:Gauge}{F H:Law G}{x y w: Legs (Lane4 G) }(u v:ℤ)(s r:ℝ)
lemma castmesh (i j:BH G)(p:QP)(h:Split x y w):
    meshZ (Ψ G s) i j (shift u r F) (shift v r H) x y p = τ (4+pitch w - u-v) r * meshZ (Ψ G (s-r)) i j F H (sr r x) (sr r y) (exp r • p):= by
    unfold meshZ; rw [figure s r,degree_sr,β_shift, β_shift, smul_neg ]; -- simp smul_neg projected
    rw [← P_ψ r _ _ _ u v (wfield i) (wfield j) (w_mass h)]; ring
lemma charmW (A:QP) (i j: BH G)(h:Split x y w):
     (∫ p,Tone.bill (exp r • A) p * meshZ (Ψ G s) i j (shift u r F) (shift v r H) x y p ∂ planeF)
        = τ (pitch w-(u+v)) r * (∫ p, Tone.bill A p * meshZ (Ψ G (s-r)) i j F H (sr r x) (sr r y) p ∂ planeF):= by
     simp_rw [castmesh u v s r i j _ h, ← Tone.Mesh.dual, mul_left_comm _ ( τ (4+pitch w-u-v) r ) ]; rw [integral_const_mul, disperse (fun p=> Tone.bill A p* meshZ ( Ψ G (s-r)) i j F H _ _ p) r, ← mul_assoc,T_add,show 4+pitch w-u-v+(-4)=pitch w-(u+v) from (by omega) ] -- `_` err
lemma Level (A:QP): Cabin (exp r • A) (Ψ G s) planeF (shift u r F) (shift v r H)= shift (u+v) r ( Cabin A (Ψ G (s-r)) planeF F H ):= by
    funext w; apply totalζ; intro l b h; simp_rw [net_sr, Tone.Mesh.dual, charmW u v s r _ _ _ h, ← Finset.mul_sum ]; ring
variable { Z J:Type}{F H:Glade G Z}
def twist (u:ℤ)(r:Z→ℝ): Glade G Z→ₗ[ℂ] Glade G Z:={
     toFun f:= fun i t=> shift u (r i) ( f i ( t - r i ) )
     map_add' F H:= by funext i t l; simp only [ Pi.add_apply,  shift,mul_add ]
     map_smul' b F:= by funext i t l; simp only [shift,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
variable {P:PUnit→ℝ} -- remove.
variable (σ: Z→ℝ)
abbrev Θ0 (G:Gauge)(Z:Type): Planet G Z:= constantP G Z ( PlanetD G ) -- Unicode emoji fail
lemma expT : expJ (constantP G Z ( PlanetD G )) (twist u σ F) (twist v σ H)= twist (u+v-4) σ (expJ (constantP G Z ( PlanetD G )) F H):= funext fun i=> funext fun t=> treesW t (σ i) u v
lemma levelW (x: Z→QP): regionC (fun _=>planeF) (fun i=>exp (σ i) • x i) (constantP G Z (PlanetD G)) (twist u σ F) (twist v σ H)= twist (u+v) σ (regionC (fun _=>planeF) x (constantP G Z (PlanetD G)) F H ):= funext fun i=> funext fun t=> Level u v t (σ i) (x i)
lemma CycleT : sailP (fun _=>planeF) (constantP G Z (PlanetD G)) (twist u σ F)= twist u σ (sailP (fun _=>planeF) (constantP G Z (PlanetD G)) F):= funext fun i=> funext fun t=> C_port t (σ i) u
end YM.MS.Port
