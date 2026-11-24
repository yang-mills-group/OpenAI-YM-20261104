import YM.MSbar.Aqua.Quartz
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable (G:Gauge){n:Side}
open Work.G05
variable {d a b C r:ℝ}{q k:ℕ}
local notation "E"=>Positions (Primary n G)
local notation "Λ"=>Native.Chart.Rail G
local notation "A"=>G.Color
local notation "Ψ"=>iteratedFDeriv ℝ
variable (v:Native.Chart.Rail G)(x:G.Color)(z:Site n→G.Color)(h:Beam G d)(he:‖x‖<d)
include h he
lemma flowsA : fderiv ℝ (Up G) x (Native.Chart.speed G v x) = -G.colorMat v.1 * Up G x+ Up G x *G.colorMat v.2:=by
    obtain ⟨hx,hb,hV,_⟩:= h x he v; have hp:= Native.Chart.breeze G v x hx; have hk:=((show DifferentiableAt ℝ (Up G) _ from G.exp_jet.differentiable (by simp) (Native.Chart.head G v (0,x))).hasFDerivAt.comp_hasDerivAt 0 hp); rw [hV] at hk; refine (hk.congr_of_eventuallyEq ?_).unique (Native.Chart.hits G v x); exact (((continuous_id.prodMk (continuous_const (y:=x))).tendsto 0).eventually hb).mono fun y hy=> (congr_arg G.mat hy).symm
lemma sailA : ContDiffAt ℝ ω (Native.Chart.speed G v) x:=((h _ he v).1.fderiv_right (by simp) |>.clm_apply (n:=ω) (g:=fun _=> (1,0)) contDiffAt_const) |>.comp (f:=fun y=> ((0:ℝ),y)) x (contDiffAt_const.prodMk contDiffAt_id) -- name
noncomputable def crest (v:Λ)(p:ℕ): A→A:= Native.Chart.speed G v-blockTaylor p (Native.Chart.speed G v)
local notation "V"=>crest G
lemma borne (w:Λ)(i:ℕ) : V (v+w) i x= V v i x+V w i x:=by
    let X:=Native.Chart.speed G; have hf:X (v+w) x=X v x+X w x:=by apply (h _ he v).2.2.2; rw [flowsA G _ x h he,map_add,flowsA G _ x h he,flowsA G _ x h he];simp [add_mul,mul_add];abel
    have hh: blockTaylor i (X (v+w)) x= blockTaylor i (X v) x+blockTaylor i (X w) x:= by unfold blockTaylor; simp only [Finset.sum_apply]; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i hi=> grok i x v w)
    unfold crest; change X (v+w) x-_=_; rw [hf,hh]; simp only [Pi.sub_apply]; abel
lemma warmth (c:ℝ)(i:ℕ) : V (c • v) i x=c • V v i x:=by
    let X:=Native.Chart.speed G; have hf:X (c • v) x=c • X v x:= by apply (h _ he v).2.2.2; rw [flowsA G _ x h he, map_smul, flowsA G _ x h he]; dsimp only [Prod.smul_fst,Prod.smul_snd]; rw [map_smul,map_smul,←smul_neg,smul_mul_assoc,mul_smul_comm,smul_add]
    have hh: blockTaylor i (X (c • v)) x=c • blockTaylor i (X v) x:=by unfold blockTaylor; simp only [Finset.sum_apply]; rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun j hj=> steeper j x v c)
    unfold crest; change X _ x-blockTaylor _ _ _=c • (X _ x-blockTaylor _ _ _); rw [hf,hh,smul_sub]
variable (i m:ℕ)
lemma vivid : ContDiffAt ℝ m (V v i) x:= ((sailA G v x h he).of_le le_top).sub ((blockTaylor_contDiff ..).contDiffAt)
noncomputable def swells (x:G.Color)(i m:ℕ): Native.Chart.Rail G→ Tensor.T G.Color G.Color m := fun y=>iteratedFDeriv ℝ m (crest G y i) x
lemma raftA : ∃ f:Λ→ₗ[ℝ] Tensor.T A A m,∀ y, f y= Ψ m (V y i) x :=by
    let X:= {y:A|‖y‖<d}; have hh:∀ᶠ y:A in 𝓝 x,‖y‖<d:= continuous_norm.continuousAt.eventually (eventually_lt_nhds he); refine ⟨{toFun:=swells G x i m, map_add':=?_, map_smul':=?_},fun y=>rfl⟩
    · intro a w; change Ψ m (V (a+w) i) x=_; rw [((show V (a+w) i=ᶠ[𝓝 x] V a i+V w i from hh.mono (fun y hz=> borne G a y h hz w i)).iteratedFDeriv ℝ m).eq_of_nhds]; exact iteratedFDeriv_add_apply (vivid G a x h he i m) (vivid G w x h he i m)
    intro c w; change Ψ m (V (c • w) i) x=c • _; rw [((show V (c • w) i=ᶠ[𝓝 x] c • V w i from hh.mono (fun y hz=> warmth G w y h hz c i)).iteratedFDeriv ℝ m).eq_of_nhds]; exact iteratedFDeriv_const_smul_apply (vivid G w x h he i m)
omit h he
structure Stone (G:Gauge)(i m:ℕ)(D B:ℝ): Prop where
   stage : 0<D
   beam : Beam G D
   positive : 0≤B
   linger (x:G.Color) : ‖x‖<D → ∀ p ≤ m,∀ v:Native.Chart.Rail G, ‖iteratedFDeriv ℝ p (crest G v i) x‖ ≤ B*‖v‖*‖x‖^(i+1-p)
lemma barn :∃ d C:ℝ,Stone G i m d C:=by
    let h:= Module.finBasis ℝ (Native.Chart.Rail G); let p:= m+i+1; obtain ⟨d,hd,hA⟩:= beeps G; choose r C hR hC hT using fun j=> remQ (p:=i) (k:=p) (by omega) ((Native.Chart.speeds G (h j)).of_le le_top)
    let f j := ((h.coord j).toContinuousLinearMap); let B:=∑ j, ‖f j‖*C j; let X:=min d (Finset.inf' (insert none (Finset.univ.image (some (α:=Fin (Module.finrank ℝ Λ))))) (by simp) (fun z=>z.elim d r)) -- nonempty triv? none syntax
    have hB:0≤B:= Finset.sum_nonneg fun y _=> mul_nonneg (norm_nonneg _) (hC y)
    have hv:0<X:=lt_min hd ((Finset.lt_inf'_iff ..).mpr (fun z _=>by cases z; exact hd; exact hR _))
    refine ⟨X,B,hv,fun x hx=>hA x (hx.trans_le (min_le_left ..)),hB,fun x hx j hj v=>?_⟩
    obtain ⟨g,hg⟩:=raftA G x hA (hx.trans_le (min_le_left ..)) i j; rw [← hg]; nth_rw 1 [← h.sum_repr v]; rw [map_sum]; unfold B; rw [Finset.sum_mul,Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun y _=>?_)); simp_rw [map_smul,norm_smul, hg]; have hd:‖f y v‖ ≤ ‖f y‖*‖v‖:= (f y).le_opNorm v
    refine (mul_le_mul hd (hT y j (by omega) x (lt_of_lt_of_le hx ?_)|>.2) (norm_nonneg _) (by positivity)).trans_eq (by ring); exact (min_le_right ..).trans (Finset.inf'_le _ (show some y∈_ from Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))))
end YM.MSbar.Aqua
