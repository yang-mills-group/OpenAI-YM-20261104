import YM.MSbar.Lis.Colors
import YM.MSbar.Lis.Pipes
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Measuring Wave
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "X"=>Positions (Primary n G)
local notation "K"=>Primary n G
variable (x i:Primary n G)(v s:G.Color)(p:ℕ)(t:Site n→G.Color)
local notation "Λ"=> Rail G
local notation "j"=>speedsK
lemma rev (v s:Native.Chart.Rail G) : Native.Chart.speed G (v+s) =ᶠ[𝓝 0] Native.Chart.speed G v+Native.Chart.speed G s:=by
    filter_upwards [armed G,Native.Chart.follows G v,Native.Chart.follows G s,Native.Chart.follows G (v+s)] with y h hx hy hv; apply h; rw [hv,Pi.add_apply,map_add,hx,hy]; dsimp only [Prod.fst_add,Prod.snd_add]; simp [add_mul,mul_add]; abel
lemma sweeping (c:ℝ)(v:Native.Chart.Rail G): Native.Chart.speed G (c • v) =ᶠ[𝓝 0] c • Native.Chart.speed G v:=by
    filter_upwards [armed G,Native.Chart.follows G v,Native.Chart.follows G (c • v)] with y h hy hx; apply h; rw [hx,Pi.smul_apply, map_smul,hy]; dsimp only [Prod.smul_fst,Prod.smul_snd]; rw [map_smul,map_smul,←smul_neg,smul_mul_assoc,mul_smul_comm,smul_add] -- names
noncomputable def ventG (p:ℕ)(b : Native.Chart.Rail G)(u:G.Color): G.Color:= Tensor.diagonal (Tensor.coeff (Native.Chart.speed G b) p 0) u
noncomputable def choir (p:ℕ)(b:Site n→ G.Color)(v: Positions (Primary n G)) :Positions (Primary n G):= Tensor.diagonal (Tensor.coeff (speedsK b) p 0) v
lemma grok (u:G.Color) (b a : Native.Chart.Rail G) : ventG p (b+a) u=ventG p b u+ventG p a u:=by
    unfold ventG Tensor.diagonal Tensor.coeff; rw [((rev b a).iteratedFDeriv ℝ p).eq_of_nhds,iteratedFDeriv_add_apply ((speeds G b).of_le le_top) ((speeds G a).of_le le_top),smul_add,_root_.add_apply]
lemma steeper (u:G.Color)(b:Native.Chart.Rail G)(c:ℝ):ventG p (c • b) u= c • ventG p b u :=by
    unfold ventG Tensor.diagonal Tensor.coeff; rw [((sweeping c b).iteratedFDeriv ℝ p).eq_of_nhds, iteratedFDeriv_const_smul_apply ((speeds G b).of_le le_top), smul_comm, _root_.smul_apply]
noncomputable def tune (k: Primary n G) : Positions (Primary n G)→L[ℝ]G.Color := (ContinuousLinearMap.proj k.1).comp (tint G _).toContinuousLinearMap
lemma speedV : ContDiffAt ℝ ω (speedsK t) 0:=by
    let F:= (tint G (Exterior.Body 1 n)).symm; apply F.contDiff.contDiffAt.comp; refine contDiffAt_pi.mpr fun i=>?_ ; let L:X→L[ℝ] G.Color:= (ContinuousLinearMap.proj i).comp F.symm.toContinuousLinearMap; exact (show ContDiffAt ℝ ω _ (L 0) from by rw [map_zero]; exact Native.Chart.speeds G (ran t i)).comp _ L.contDiff.contDiffAt
lemma compass (u:X) (i:Primary n G) : choir p t u i= ventG p (ran t i.1) (tune i u) i.2:=by
    let L:= tune i; suffices h: L (choir p t u)= ventG p (ran t i.1) (L u) by exact congrArg (fun z:G.Color=> z i.2) h
    unfold choir ventG; rw [Tensor.diagonal,←Tensor.coeff_linear L _ ((speedV t).of_le le_top)]; let f:= Native.Chart.speed G (ran t i.1); have hx: L ∘ speedsK t=f ∘ L:=rfl
    rw [hx,Tensor.diagonal, Tensor.coeff,Tensor.coeff, _root_.smul_apply, _root_.smul_apply]
    have hg:ContDiffAt ℝ p f (L 0):= by rw [map_zero]; exact (speeds ..).of_le le_top
    apply congr_arg (_ • ·); rw [map_zero] at hg; have he : ContDiffAt ℝ p (f ∘ L) 0 := ((map_zero L).symm ▸ hg : ContDiffAt ℝ p f (L 0)).comp _ (L.contDiff.contDiffAt); change Tensor.diagonal (iteratedFDeriv ℝ p (f ∘ L) 0) u=Tensor.diagonal (iteratedFDeriv ℝ p f 0) (L u); rw [← Next.Foundations.iteratedDeriv_on_line he, ← Next.Foundations.iteratedDeriv_on_line hg]; simp only [Function.comp_def,map_smul]
lemma tuning (i v:Primary n G) : tune i (bolt v) = if i.1=v.1 then sun G v.2 else 0:=by
   ext k; split; next hx=>
       change bolt v (i.1,k)= sun G v.2 k; rw [hx]; cases v; simp [bolt,sun,Pi.single_apply]
   next hx=> change bolt v (i.1,k) = 0; rw [show bolt v (i.1,k)=0 from (by rcases i with ⟨i,x⟩; rcases v with ⟨v,y⟩; change i ≠ v at hx; simp [bolt,Pi.single_apply,hx])] -- simp [bolt]; rintro h; apply hx; exact congr_arg Prod.fst h -- simp order
noncomputable def compassS (p:ℕ)(b : Native.Chart.Rail G)(z:G.ColorIndex)(u:G.Color):=ventG p b u z
lemma compass_sm (b: Native.Chart.Rail G)(z:G.ColorIndex)(p:ℕ): ContDiff ℝ ω (compassS p b z):= by unfold compassS ventG; exact (EuclideanSpace.proj z : G.Color →L[ℝ] ℝ).contDiff.comp (Tensor.diag_smooth (Tensor.coeff (Native.Chart.speed G b) p 0) ω)
def allot (i: Primary n G)(L:List (Primary n G)):Prop:= ∀ t∈L,i.1=t.1
noncomputable def cobble (G:Gauge)(l:List G.ColorIndex): List G.Color:= l.map (sun G)
variable (L:List (Primary n G))
lemma pattern (b:Site n→ G.Color) : buoy (fun v=> choir p b v i) 0 L=if allot i L then roc (compassS p (ran b i.1) i.2) (L.map fun s=>sun G s.2) 0 else 0:=by
    let f:=compassS p (ran b i.1) i.2; let v:=tune i; have hp:ContDiff ℝ ω f:=compass_sm ..; unfold buoy; rw [show (fun m:Positions (Primary n G)=>choir p b m i)= f ∘ v from funext fun v=> compass p b v i, toe v (L.map bolt).length _ (hp.contDiffAt.of_le le_top) le_rfl ,map_zero,List.map_map] -- implicit instance orientation he
    split; next hm=>
       congr 1; apply List.map_congr_left; intro t ht; exact (tuning i t).trans (if_pos (hm t ht))
    next hm=>
       unfold allot at hm; push Not at hm; obtain ⟨t,ht,hM⟩:= hm; apply Lis.emptyF L.length _ _ (List.mem_map.mpr ⟨_,ht,(tuning i t).trans (if_neg hM)⟩) (hp.contDiffAt.of_le le_top) (by simp)
end YM.MSbar.Lis
