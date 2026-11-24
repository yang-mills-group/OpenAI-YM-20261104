import YM.OPE.Compatible.Lumen.Dash
/-!
# Dx in distinguished diagram. Onto full gauge directions, no ghost determinant assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer
open PertExtension Series Asymptotics
attribute [local instance] Gauge.frobInner
namespace Score
variable {V D:Type}{B:Set V} {S:Score D V}[Fintype D]
local notation "XD" => Keys G D
nonrec def galaxy (S:Score D V) (G:Gauge) : Keys G V→ₗ[ℝ] Keys G D where
   toFun a p := a (S.inn p)-a (S.out p)
   map_add' a b:= by ext i; simp only [Pi.add_apply,PiLp.add_apply,PiLp.sub_apply]; abel
   map_smul' a b:=by ext i; simp only [Pi.smul_apply,PiLp.smul_apply,PiLp.sub_apply, RingHom.id_apply];rw [smul_sub]
omit [Fintype D] in lemma gemZero (d:D)(a:ℝ→Keys G D)(g:a 0=0)(b:XD)(h:HasDerivAt a b 0): HasDerivAt (fun t=> G.mat (put (a t) d)) (G.colorMat (b d)) 0:=by
     have he:= G.expDiff_zero; exact ((show a 0 d=0 from congr_fun g d).symm ▸ he : HasFDerivAt (fun x:G.Color=>G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap (a 0 d)).comp_hasDerivAt 0 ((hasDerivAt_pi.mp h) d)
lemma gram_diff [Fintype V](x y:ℝ→Keys G D)(s:ℝ→ Tile G V)(u w:Keys G D)(h:S.Track x y s)(he:s 0=1)(htx:HasDerivAt x u 0)(hty:HasDerivAt y w 0) (hb: Tendsto s (𝓝 0) (𝓝 1)): ∃ t:Keys G V,S.galaxy G t+u=w:= by
    let g(i:V)(x:ℝ):= G.plog (G.mat (s x i))
    have hg0(i:V): g i 0=0:= by simp [g,he]
    let t (i: V) := fderiv ℝ (g i) 0 1; have hg(i:V): HasDerivAt (g i) (t i) 0:= ((by exact ((show ContDiffAt ℝ ∞ G.plog (G.mat (s 0 i)) from by rw [he,Pi.one_apply,G.mat_one]; exact G.plog_diff.of_le le_top).comp (f:=fun t=>G.mat (s t i)) 0 (h.chart i)).differentiableAt (by simp): DifferentiableAt ℝ (g i) 0) |>.hasFDerivAt).hasDerivAt
    have hgm(i:V): HasDerivAt (fun x=> G.mat (s x i)) (G.colorMat (t i)) 0:= by
        apply (((hg0 i).symm ▸ G.expDiff_zero : HasFDerivAt (fun x:G.Color =>G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap (g i 0)).comp_hasDerivAt 0 (hg i) : HasDerivAt ((fun x:G.Color =>G.mat (G.lieExp x)) ∘ g i) _ _).congr_of_eventuallyEq
        filter_upwards [(tendsto_pi_nhds.mp hb i).eventually G.plog_right] with x hx; exact congr_arg G.mat hx.symm
    refine ⟨t,?_⟩; funext i
    let f(z:ℝ):= s z (S.inn i); let ℓ(z:ℝ):= s z (S.out i); let P(z:ℝ):= put (x z) i
    have hez := (hgm (S.inn i) |>.mul (gemZero i x h.gx u htx)|>.mul (hgm (S.out i) |>.star)); simp only [Pi.mul_apply,he, h.gx,put_zero,Pi.one_apply,G.mat_one,mul_one,one_mul,star_one] at hez -- shadow
    have hY : _ =G.colorMat (w i):= hez.unique ( (gemZero i y h.gy w hty).congr_of_eventuallyEq ?_)
    swap
    · filter_upwards [h.law] with p hv; specialize hv; have hh : put (y p) i = f p*P p*(ℓ p)⁻¹:= congr_fun hv.symm i
      rw [hh,G.mat_mul,G.mat_mul,G.mat_inv]; rfl
    apply G.colorMat_injective; rw [← hY, G.colorMat_skew]; change G.colorMat (t _ -t _+ u i)=_; rw [map_add,map_sub]; abel
namespace Stand
variable (T:S.Stand B) [Fintype V]
lemma normal_arc (u:XD):∃ t,(S.galaxy G t) + T.rollX (T.slab G u)= T.dtex G u:=by
     let A:= T.skews G; let f:=fun t:ℝ=>t•u; have hf:HasDerivAt f u 0:= by simpa only [one_smul] using! ((hasDerivAt_id' (0:ℝ)).smul_const u)
     let g:=fun t:ℝ=> (T.setMove (T.splitSet (put (t•u))))⁻¹
     have he: g 0=1:=by simp [g,setMove,show T.splitSet (1:Tile G D)=1 from rfl]
     refine gram_diff _ _ g _ _ (T.pathZ u) he ?_ ?_ ?_
     · simp_rw [map_smul]; exact (show HasDerivAt (fun t : ℝ=> t • T.rollX (T.slab G u)) _ 0 from by simpa only [one_smul] using! ((hasDerivAt_id' (0:ℝ)).smul_const (T.rollX (T.slab G u))))
     · let L:=T.dtex G; have hk:f 0=0:=zero_smul ..; exact ((show HasFDerivAt A.gradient L (f 0) from hk.symm ▸ (A.gradC.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hf)
     have hh:Continuous g:= by
          have hd:Continuous (fun x:T.Stable→G.El=> T.cite x (1:T.Free→G.El)):= T.citeC.comp (continuous_id.prodMk continuous_const); let a:=fun x:ℝ=>T.splitSet (put (x•u)); have he:Continuous a:= continuous_pi fun i=> (continuous_apply _).comp (putC.comp (continuous_id.smul continuous_const)); exact (T.sweepC.comp (hd.comp he)).inv
     exact he ▸ hh.tendsto _
end Stand
end Score
end YM.OPE.Cascade
