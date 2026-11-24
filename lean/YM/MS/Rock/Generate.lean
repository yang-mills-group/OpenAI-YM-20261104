import YM.MS.Rock.Plus
/-!
# Ordinary-addon functions bilinear stably

Supply rank merom committees later. Expose equivalence for support. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock.Oceans
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Path Landau Arts Pilot Spin Arc Wire
open Metric
open scoped Topology ContDiff
variable {G:Gauge}{b c: Bool}{F H L:Mob G}{U V W:Rip G}
variable (hU: Knot b U)(hF : Form0 b F)(hV:Knot b V)(hH: Form0 b H){i:ℂ}(hi:i∈Town) (c:ℂ)
include hi hF hH hV hU
lemma pool_add (he:∀ (m:ℕ)(p:SectorP m)(l:Legs (Shore G m)), Wtr i W L p l=Wtr i U F p l+Wtr i V H p l): ocean i W L=ocean i U F+ocean i V H:= by
   funext m l; let K:( (SectorP m × ℝ)×ℝ→ℂ)→ Arc.Tree ℝ ℂ:= carpet (Px m); let r:= ray l; let X:= wing i W L r; let V0:=wing i U F r; let Y:=wing i V H r; have he:X= V0+Y:=funext fun x=>he ..;
   have hx : K X=K V0+K Y:= by rw [he]; ext q; exact integral_add ((Q.Gmajor (Px m) (exact_test hF.price hU.price r i) ()).values q) ((Q.Gmajor (Px m) (exact_test hH.price hV.price r i) ()).values q) -- Q ambiguous?
   change coreC _ _ (K X) _=coreC _ _ (K V0) _+coreC _ _ (K Y) _; rw [hx, core_pl (carpet_test hF.price hU.price _ _) (mirror_r _ (wing_mirror hF.token hU.token i r)) (carpet_test hH.price hV.price _ _) (mirror_r _ (wing_mirror hH.token hV.token i r)) hi]; rfl
omit hi hH hV in
lemma pool_m (he:∀ (m:ℕ)(p: SectorP m)(l:Legs (Shore G m)),Wtr i W L p l=c • Wtr i U F p l): ocean i W L=c • ocean i U F := by
   funext m l; let K:( (SectorP m × ℝ)×ℝ→ℂ)→ Arc.Tree ℝ ℂ:= carpet (Px m); let w:=ray l; let X:= wing i W L w; let V:=wing i U F w
   have H0:X=c • V:= funext fun x=> he ..; have hv: K X= c • K V:= by rw [H0]; funext x; unfold K carpet; simp_rw [Pi.smul_apply, integral_smul]
   change coreC _ _ (K X) _= c • coreC _ _ (K V) _; rw [hv,core_m (carpet_test hF.price hU.price _ _)]; rfl
omit hV in
lemma oceanR : ocean i U (F+H)=ocean i U F+ocean i U H:= by
   apply pool_add hU hF hU hH hi; intro m p l; simp only [Wtr,yeast,token,fleck,map_add,Pi.add_apply,Pi.smul_apply, mul_add, Finset.sum_add_distrib, smul_add, at_trc]; abel
omit hH in
lemma oceanL : ocean i (U+V) F=ocean i U F+ocean i V F:= by
    apply pool_add hU hF hV hF hi; intro m p l; simp only [Wtr,yeast,token,fleck,Pi.add_apply,Pi.smul_apply,add_mul,Finset.sum_add_distrib,smul_add, at_trc]; abel
omit hH hV hi in
lemma scaleR: ocean i U (c • F)=c • ocean i U F:= by
    apply pool_m hU hF c; intro m p l; simp only [Wtr,yeast,token,fleck,at_trc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; simp_rw [mul_left_comm (_:ℂ) c, ← Finset.mul_sum]; ring
omit hH hV hi in
lemma scaleL: ocean i (c • U) F=c • ocean i U F:= by
    apply pool_m hU hF c; intro m p l; simp only [Wtr,yeast,token,fleck,at_trc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; simp_rw [mul_assoc c, ← Finset.mul_sum]; ring
-- z acceleration useful for λ_a derivatives and commute over Ccy
end YM.MS.Rock.Oceans
