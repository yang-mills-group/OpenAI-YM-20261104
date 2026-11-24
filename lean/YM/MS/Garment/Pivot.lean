import YangMills.WilsonProof.NativeSupport.YM.MS.Garment.Quanta
/-!
# Derivative of Γ-grid at real log lengths.

Chunk statement: support area supplied pointwise (even off horizon), germ later mask truncate all-order. Does not assume Pose closed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wave
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric Color Book Convolve Signal Wick
open scoped Topology ContDiff
variable {G:Gauge}{x:ℂ}(k:ℂ) (s:ℝ){m n N:ℕ}
variable {F H P R:ℝ→ T (Mob G)}{K:ℝ→Mob G}{X Y: Mob G}
local notation "V" t => γ x k t G -- not `term` binder parser? test
lemma J_turn (h:x∈Town)(hv:∀ s,Form0 false (K s))(hr:Form0 false X)(hp: Curve K X s): speed (fun t=> (V t).J (K t)) ((V s).J X+(V s).L (K s)) s:= by
    let Q:= Wick.Q G; have hm := hp.heard (vex_caps G s) hv hr (fun t=>(B_caps ..).clearer) (C_caps G s|>.clearer) h
    have ht:=speed_add (speed_port hp.valid Q) (speed_mul hm.valid k);
    simp only [γ,LinearMap.add_apply,LinearMap.smul_apply,port_spec h _ (B_caps .. |>.clearer) (hv _), port_spec h _ (B_caps G s|>.clearer) hr,port_spec h _ (C_caps G s|>.clearer) (hv _)];
    convert! ht using 1; -- add order
    simp [smul_add,add_assoc]; rw [add_comm (k • ocean x (B0 G s) X), upcoming]
lemma C_turn {X' Y':T (Mob G)} (n:ℕ) (hx:∀ i≤ n, Curve (fun t=> F t i) (X' i) s)(he:∀ i≤n,Curve (fun t=> H t i) (Y' i) s):
    speed (fun t=> pairW (V t).C (F t) (H t) n) ((pairW (V s).D (F s) (H s)+pairW (V s).C X' (H s)+pairW (V s).C (F s) Y') n) s := by
    simp only [paired, Pi.add_apply, ← Finset.sum_add_distrib]; refine speed_sum _ (fun i h=>?_); obtain hz:=Finset.mem_antidiagonal.mp h; exact speed_arbor (hx i.1 (by omega)|>.valid) (he i.2 (by omega)|>.valid) ( trigger G s) (reverse_b G) (reverse_c G s)

-- derivative at point: use Cast from full supported not include $n$ anymore
lemma mat0 (n:ℕ)(l : Legs (Shore G m))(hp:net l=0)(h:x∈Town)(hc:Cast (F s) (F s))(hF:∀ t i,Form0 false (F t i))(hk:∀ i≤ n, Form0 false ((V s).grow (F s) i))(hu:∀ i≤ n, Curve (fun t=> F t i) ((V s).grow (F s) i) s): HasDerivAt (fun t=> (V t).matCont (F t) n m l) ((V s).lives (F s) ((V s).matCont (F s)) n m l) s:= by
    let M:= (V s).grow (F s); obtain ht:= (J_turn k s h (K:=fun r=> F r n) (fun t=>hF t n) (hk n le_rfl) (hu n le_rfl)); have hW := (C_turn (x:=x) k s n (F:=F) (H:=F) hu hu); obtain hp := congr_fun (point_B k s h hp hc) n; refine ?_ ; change HasDerivAt _ ((promote (slice l) ((V s).lives (F s) ((V s).matCont (F s)))) n) s; rw [← hp]; --  ((V s).lives _ _ _ _ _)=_ from hp.symm]; convert! ((ht m l).add ((hW m l).const_mul ((2:ℂ)⁻¹))) using 1; -- swaps
    convert! ((ht m l).add ((hW m l).const_mul ((2:ℂ)⁻¹))) using 1
    simp only [promised,slice,Pi.add_apply, Pi.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]; ring
lemma res0 (n:ℕ)(h:x∈Town)(hc:Cast (F s) (H s))(hF:∀ t i,Form0 false (H t i))(hk:∀ i≤ n, Form0 false ((V s).lives (F s) (H s) i))(hp:∀ i≤ n, Curve (fun t=>F t i) ((V s).grow (F s) i) s)(hu:∀ i≤ n,Curve (fun t=> H t i) ((V s).lives (F s) (H s) i) s): speed (fun t=> (V t).res (F t) (H t) n) (((V s).lives (F s) ((V s).res (F s) (H s)) + pairW (V s).X ((V s).matCont (F s)) (H s)) n) s:=by
   obtain ht:= speed_add ( J_turn k s h (K:=fun t=>H t n) (fun t=>hF t n) ( hk n le_rfl) (hu n le_rfl)) ( C_turn (x:=x) k s n hp hu)
   rw [←point_M k s h hc]; convert! ht using 1; simp only [GridR.res,Pi.add_apply,promised]; abel -- missing M window? check formula point_M vs RHS H derivative.
end YM.MS.Garment.Wave
