import YM.MS.Garment.Quanta
import YM.MS.Garment.SphereX
/-!
# All integer angular analytic derivation of D formal amplitudes

Statement limited to any supported all-order arrays (zero padding for germs at n), not
 convergence or uniform bounds. Basis primitive for Ward calculus.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wave
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric Color Book Convolve Signal Wick
open scoped Topology ContDiff
variable {G:Gauge}{x:ℂ}(k:ℂ)(s:ℝ){F H: ℕ→ Mob G} {m n:ℕ}{l:Legs (Shore G m)}
local notation "V" => γ x k s G
structure Cast (F H : ℕ→ Mob G): Prop where
   f k: Form0 false (F k)
   g k: Form0 false (H k)
   order k: Rock.sym (F k)
   order' k: Rock.sym (H k)
   level k: tide (F k)
lemma elementC {E:Type*}[AddCommGroup E][Module ℂ E] (P:LM (Mob G) E)(h:x∈Town)(hm:Cast F H): GridR.Elements P V F H := by
   refine ⟨fun i=> congr_arg P (Truss k s h (hm.g _) (hm.order' _)), fun i j=> congr_arg P (quad0 k s h (hm.f _) (hm.g _) (hm.order _) (hm.order' _) (hm.level _)), fun i j l=>?_⟩; apply congr_arg; funext v; exact axis_press (cl_a G s v) (cl_b G s v) (hm.order i v) (hm.level i v) (hm.order j v) (hm.level j v) (hm.order' l v)
-- plane Charge extraction $κ linear$
lemma board0 (F H:ℕ→ Mob G) (U: Oceans.Pair G)(he:∀ i j, U (F i) (H j) m l=U (H j) (F i) m l): promote (slice l) (pairW U F H) = promote (slice l) (pairW U H F):= by
    funext n; simp only [promised,paired,slice,LinearMap.comp_apply,LinearMap.proj_apply,Finset.sum_apply]; simp_rw [he]; rw [← Finset.Nat.sum_antidiagonal_swap]; rfl
lemma point_B (h:x∈Town)(hv:net l=0)(hk:Cast F F): promote (slice l) (promote (V).J ((V).grow F) + promote (V).L F +(2:ℂ)⁻¹ • (pairW (V).D F F+pairW (V).C F ((V).grow F)+ pairW (V).C ((V).grow F) F))= promote (slice l) ((V).lives F ((V).matCont F)):= by
    apply GridR.bright_mat (elementC k s _ h hk);
    swap
    · apply board0; intro i j; refine axis_comm (cl_b G s m) (hk.level i m) ?_ hv; change Pure (field Landau.parity) false (pairW (V).X F F j m); rw [paired, Finset.sum_apply]; exact Pure.sum (antidiagonal j) (fun u _=> tree_pure (cl_a G s m) (hk.level u.1 m) (hk.level u.2 m))
    all_goals exact board0 _ _ (V).X (fun i j=> (axis_even (cl_a G s m) (hk.level i m) hv).symm)
lemma point_M (h:x∈Town)(hk:Cast F H): (V).res F ((V).lives F H)+promote (V).L H+pairW (V).D F H+pairW (V).C ((V).grow F) H= (V).lives F ((V).res F H)+pairW (V).X ((V).matCont F) H:= by exact (elementC k s LinearMap.id h hk).lights -- order
end YM.MS.Garment.Wave
