import YM.OPE.Compatible.Swoon.Pea
/-!
# cumulants/hats parser
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Coin
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset Matrix LinearMap Flock
variable {E F Y I:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
def τ4 (P:R4 F)(x:F):ℝ:= P ![x,x,x,x]/24
def τ21 (P:R4 F)(x:F)(A:E→L[ℝ] F)(i:E):= P ![x,x,A i,A i]/4
lemma τAve (U:R4 F)(h:Tensor.Sym U)(x:F)(A:E→L[ℝ] F):
 L.average μ (fun i:E=> τ4 U (x+A i))= τ4 U x + L.average μ (τ21 U x A)+L.average μ (fun i=>τ4 U (A i)):=by
    let P(i:E):= U ![A i,x,x,x]; let Q:= τ21 U x A; let D(i:E):= τ3 (bang U x) A i; let s:= (6:ℝ)⁻¹ • P+D; let w(i:E):= τ4 U (A i)
    have hw:Bond w:=by
        unfold w τ4; simp_rw [div_eq_mul_inv]; apply Bond.mul (v:=fun _=>(24:ℝ)⁻¹) _ (Bond.keep _); convert Bond.multiline U (fun _ : Fin 4=> (A:E→F)) (fun _ c=> Bond.glyph (c.comp A.toLinearMap)) using 1; funext i; apply congr_arg; ext1 j;fin_cases j<;>rfl
    have hL:∃ V:E→ₗ[ℝ] ℝ,P=V:=by
        refine ⟨{toFun:=P,map_add':=?_,map_smul':=?_},rfl⟩; intro i j;unfold P; rw [map_add]; exact DFunLike.congr_fun (U.curryLeft.map_add (A i) (A j)) ![x,x,x]
        intro c i; unfold P; rw [map_smul]; exact DFunLike.congr_fun (U.curryLeft.map_smul c (A i)) ![x,x,x]
    obtain ⟨V,hV⟩:= hL; have hs:Bond s:= (Bond.scale _ (show Bond P from hV.symm ▸ Bond.glyph V)).add ((τBond (bang U x) x A).2); have hQ:Bond Q:=by
        convert Bond.scale (2:ℝ)⁻¹ ((τBond (bang U x) x A).1) using 1; funext i; change _/4=(2:ℝ)⁻¹*(U _/2); change _=(2:ℝ)⁻¹*(U ![x,x,A i,A i]/2); ring
    change L.average μ _= _+ _+L.average μ w; have hS(a:E):s (-a)= -s a:=by unfold s; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hV,map_neg,D,τLow]; ring
    rw [show (fun i:E=> τ4 U (x+A i)) =(fun _=> τ4 U x)+Q+w+s from ?_,sun _ _ (((Bond.keep _).add hQ).add hw) hs,sun _ _ ((Bond.keep _).add hQ) hw,sun _ _ (Bond.keep _) hQ, singleConst, colorful μ L _ hs hS,add_zero]
    funext i; change _ = _ +Q i+ w i+ ((6:ℝ)⁻¹ * P i+D i); unfold w D P Q τ4 τ21 τ3;rw [buck4 U _ _ h]; rw [show (bang U x) _ = U ![x,A i,A i,A i] from rfl];ring
private lemma bothM (f g:E→ℝ)(h:Bond f)(hp:Bond g):L.average μ ((f+g)^2) =L.average μ (f^2)+ 2*L.average μ (f*g)+L.average μ (g^2):=by
    have he:= h.mul hp; rw [show (f+g)^2=f^2+(2:ℝ) • (f*g)+g^2 from ?_,sun _ _ ((h.pow 2).add (Bond.scale _ he)) (hp.pow 2),sun _ _ (h.pow _) (Bond.scale _ he),scooted]; funext i; simp only [Pi.add_apply,Pi.pow_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul];ring
lemma τWool (U:R3 F)(h:Tensor.Sym U)(x:F)(A:E→L[ℝ] F)(v:E)(hv:τ1 U x A=(-2:ℝ)⁻¹ • L.P v):
     let s:= fun i=>τ0 U (x+A i)
     let c:= τ2 U x A
     L.average μ (s^2)-(L.average μ s)^2 - L.average μ ((τ3 U A)^2)= L.P v v/4 + (L.average μ (c^2)-(L.average μ c)^2) - L.average μ (τ2 U (A v) A):=by
         intro s c; let d:= τ3 U A; let α:E→ℝ:= fun _=> τ0 U x; let q:= τ1 U x A; let Q:= ⇑q; have hq : Q=(-2:ℝ)⁻¹ • ⇑(L.P v):=by unfold Q q; rw [hv];rfl
         let b:=α+c; let k:=Q+d; have hk: s=b+k:=by
              unfold b k; have hp : s=α+Q+c+d:=τEcho U h x A; rw [hp]; ring
         obtain ⟨hx,hy⟩:= τBond U x A; have ht:Bond α:= Bond.keep _; have hz:Bond Q:= Bond.glyph q; have hh:Bond b:= ht.add hx; have hK:Bond k:=hz.add hy
         have hc:L.average μ ((L.P v: E→ℝ) * d)= L.average μ (τ2 U (A v) A):=τipp μ L U h v A
         have he(i:E): k (-i)= - k i:=by unfold k Q d; simp only [Pi.add_apply, map_neg,τLow]; ring
         change _-_ - L.average μ (d^2)=_ ; rw [hk,bothM μ L _ _ hh hK,sun _ _ hh hK, colorful _ _ _ hK he,colorful _ _ (b*k) (hh.mul hK) (fun i=>by simp only [Pi.mul_apply,he,b,α,c,Pi.add_apply, τSteep]; ring)]; unfold b k; rw [sun _ _ ht hx,bothM μ L _ _ ht hx,bothM μ L _ _ hz hy]
         rw [show α^2=fun _=> (τ0 U x)^2 from funext fun i=>by unfold α;simp, singleConst,singleConst, show α*c=τ0 U x • c from rfl,scooted,hq,smul_mul_assoc,scooted,hc]
         rw [show (((-2:ℝ)⁻¹ • ⇑(L.P v))^2)= (4:ℝ)⁻¹ • (⇑(L.P v)*⇑(L.P v)) from ?_, scooted,summer,show L.wick (L.P v) (L.P v)=L.P v v by simp [Law.wick]];ring
         funext i; simp only [Pi.pow_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul];ring
end YM.OPE.Libra.Coin
