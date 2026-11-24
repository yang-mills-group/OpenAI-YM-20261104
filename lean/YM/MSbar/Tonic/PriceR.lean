import YM.MSbar.Tonic.Plates
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tonic
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c f:Side}{S:StepData c f}
local notation "J"=> Positions (Primary c G)
local notation "X"=> Primary c G
local notation "Q"=> Config G f
variable (β t:ℝ)(U:Config G f)(M:Config G c)(v:S.Choices)
local notation "B₀"=> tribe S β t U v
local notation "Φ"=> wing S U v
variable (x:Positions (Primary c G))(L:List (Primary c G))(i j:Primary c G)(e:Bond c)
-- absorb |β| polynomial bound fixed D, uniform link cost. independent of period and positions. ratio ∂ along X.SetΦ
noncomputable def bend (U:G.Mat)(a:ℝ)(x:G.Color):= a*(1-(Matrix.trace (G.mat (G.lieExp x)*U)).re / G.repDim)
lemma patch (a:ℝ) : ContDiff ℝ ω (fun x:G.Mat × G.Color=>bend x.1 a x.2):=by
     let f:G.Mat→L[ℝ]ℂ:= (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap; let L:=Complex.reCLM.comp f
     have hx:ContDiff ℝ ω (fun v:G.Mat×G.Color=>G.mat (G.lieExp v.2)*v.1):=(G.exp_jet.comp (f:=Prod.snd) contDiff_snd).mul contDiff_fst
     unfold bend; exact ContDiff.mul contDiff_const (ContDiff.sub contDiff_const ((L.contDiff.comp hx).div_const _))
variable {p:ℕ}{K B:ℝ}
structure PriceR (G:Gauge)(p:ℕ)(B:ℝ): Prop where
    pos :0≤B
    paid (x:G.El)(a:G.Color): ‖a‖ ≤ 1 → ∀ i≤p, ‖iteratedFDeriv ℝ i (bend (G.mat x) 1) a‖ ≤ B
private lemma sliceA {E M: Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup M][NormedSpace ℝ M] {W:E× M→ℝ} {x:E}{y:M}(hx:Allows p W (x,y) B) : ∀ i:ℕ,i≤p→ ‖iteratedFDeriv ℝ i (fun y=>W (x,y)) y‖ ≤ B:=by
     intro i hi; let T:M→L[ℝ](E× M):= (0:M→L[ℝ] E).prod (ContinuousLinearMap.id ..)
     have ht: ‖T‖ ≤1:=by apply T.opNorm_le_bound zero_le_one; intro z; change ‖((0:E),z)‖ ≤ _; simp
     let fE(v:M):=W (x,v); let f(z:E× M):= W ((x,y)+z); have hG : f ∘ T=(fun z=> fE (y+z)):= by funext z; change W ((x,y)+(0,z))=_;rw [Prod.mk_add_mk, add_zero]
     have hu:ContDiffAt ℝ i f (T 0):=by
        have ht : (x,y)+ T 0=(x,y):=by rw [map_zero,add_zero]
        exact ((ht.symm ▸ hx.1 : ContDiffAt ℝ ω W ((x,y)+T 0)).of_le le_top).comp (T 0) (f:=fun z=> (x,y)+z) (contDiffAt_const.add contDiffAt_id)
     rw [show iteratedFDeriv ℝ i fE y= iteratedFDeriv ℝ i (f ∘ T) 0 from ?_,iter_lin_at hu,map_zero]; swap
     · rw [hG, iteratedFDeriv_comp_add_left,add_zero] -- name
     unfold f; rw [iteratedFDeriv_comp_add_left, add_zero]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; rw [prod_const,card_univ,Fintype.card_fin]; exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht)).trans (hx.norm_le _ hi)
lemma price_r (G:Gauge)(p:ℕ) :∃ B:ℝ, PriceR G p B:=by
     let W(x:G.Mat×G.Color):= bend x.1 1 x.2; have hv:ContDiff ℝ ω W:= Tonic.patch _; let q:= (Set.range G.mat) ×ˢ (Metric.closedBall (0:G.Color) 1); have he:IsCompact q:=(isCompact_range G.continuous_mat).prod (isCompact_closedBall ..)
     obtain ⟨B,hB,hp⟩:=exists_allows he (fun z _=>hv.contDiffAt) p; refine ⟨B,hB,fun x a hx i hi=>?_⟩
     exact sliceA (hp (G.mat x,a) (show _∈ q from ⟨⟨_,rfl⟩,by simpa using hx⟩)) i hi
-- costs β real.Q
noncomputable def tintB (G: Gauge)(e: Bond c): Positions (Primary c G)→L[ℝ]G.Color:= (ContinuousLinearMap.proj (φ:=fun _ : Body 1 c=> G.Color) (R:=ℝ) (e.1,Exterior.coord e.2)).comp (tint G _).toContinuousLinearMap
lemma bar (e:Bond c){R:G.Mat} (a:ℝ) : rowS G a t e R= bend R a ∘ (t • tintB G e: Positions X→L[ℝ] G.Color):=by
     funext z; have he: postcard G c t z e=G.lieExp (t • tintB G e z):= (Work.F03.represent_link _ _).trans (congr_arg G.lieExp (show _= t • tintB G e z from (by rw [map_smul];rfl)))
     unfold rowS; rw [he];rfl
lemma rung (e:Bond c)(z:G.Mat) (l:List (Primary c G))(i:Primary c G)(he:e ≠ Lis.rope i) : buoy (rowS G 1 t e z) x (l++[i])=0:=by
      let f:= bend z 1; let V:J→L[ℝ]G.Color:= t • tintB G e; unfold buoy; let p:= l.length+1; have hh:ContDiffAt ℝ p f (V x):= ((patch (G:=G) (1:ℝ)).comp (f:=fun x:G.Color=>(z,x)) (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le le_top; let Z:= l ++ [i]
      rw [bar, toe V p _ hh (by unfold p; simp), List.map_append,List.map_append,List.map_cons,List.map_cons]; apply Lis.emptyF p _ _
      · refine List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl ?_))); have hv: tintB G e (bolt i)= (0:G.Color):=by
           ext k; change bolt i (primary e k)=0; have he':primary e k ≠ i:=by intro hg; rw [← hg,Lis.curb] at he; exact he rfl
           simp [bolt,he']
        rw [show V _=t • tintB G e (bolt i) from rfl,hv,smul_zero] -- orientation
      · exact hh
      unfold p; simp
variable (h : PriceR G p K)(hp : |t| ≤1)(hx:shade G*|t| *‖x‖≤1)(hl:L.length < p)
include h hp hx hl
noncomputable def stampR (G: Gauge)(K:ℝ)(p:ℕ) := K*(shade G)^p
lemma rowPrice (d:Bond c) (v:G.El)(i:Primary c G) : |buoy (rowS G 1 t d (G.mat v)) x (L++[i])|≤ stampR G K p:=by
      let f:= bend (G.mat v) 1; let T:= tintB G d; let W:=t • T; have ht:‖T‖≤ shade G:=by apply T.opNorm_le_bound (shade_pos G|>.le); exact fun z=> (norm_le_pi_norm ((tint G _) z) _).trans (tint_le z)
      have hv:‖W‖ ≤ |t| *shade G:=by unfold W; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ht (norm_nonneg _); -- |t|.Lean.ok
      have hW:‖W x‖ ≤1:= (W.le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hv.trans_eq (mul_comm ..)) (norm_nonneg _)).trans hx)
      have hh : ContDiff ℝ (↑p) f:= ((patch (G:=G) 1).comp (f:=fun x:G.Color=>(G.mat v,x)) (contDiff_const.prodMk contDiff_id)).of_le le_top; unfold buoy; let l:= L++[i]; have hl':l.length≤p:=by unfold l; simp [hl]; -- l ≤p
      rw [bar, RawP.fEntry (f:= bend (G.mat v) 1 ∘ (t • tintB G d:J→L[ℝ] G.Color)) ((hh.comp W.contDiff).contDiffAt) (L++[i]) hl']; -- signature and hF
      change ‖entry (f∘ W) x ((L++[i]).get)‖ ≤ _; apply le_trans (entry_bound ..); unfold stampR; rw [iter_lin_at]; rotate_left
      · exact hh.contDiffAt.of_le (Nat.cast_le.mpr hl')
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_; rw [prod_const,card_univ,Fintype.card_fin]; apply mul_le_mul; exact h.paid v _ hW _ hl'; exact (pow_le_pow_left₀ (norm_nonneg W) (hv.trans (mul_le_of_le_one_left (shade_pos G|>.le) hp)) _).trans (pow_le_pow_right₀ (shade_one ..) hl'); positivity; exact h.pos
end YM.MSbar.Tonic
