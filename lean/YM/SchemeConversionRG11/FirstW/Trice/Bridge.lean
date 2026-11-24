import YM.SchemeConversionRG11.FirstW.Trice.Tile
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{x:Nodes}{W:Wash}{R ρ r :ℝ}
def spray (g:P→Badge G)(j:P):Axis→ E4 → G.Color:=toast (g j) (glow j) (x j)
abbrev foreL (j:P):=Triad.slide j
abbrev aft (j:P):=Triad.lag j
abbrev kS (g:P→Badge G):=fun i:P=>unitColor G (g i).2
variable (g:P→Badge G)(j:P)(i m a b:Axis)
def centerK (g:P→ Badge G)(j:P)(m a b:Axis):= stove (fun t=>(g t).1) (orderP j m a b)
local notation "PI" => spray (x:=x) g
lemma limb (v:E4)(i:P)(m a b:Axis): PI i (orderP j m a b i) v= leg x (centerK g j m a b) 0 i v • kS g i := rfl
lemma origG (v:E4): Triad.surface x (centerK g j m a b) j i 0 v= Triad.surface x (centerK g j m b a) j i 0 v:= by unfold Triad.surface; congr 2 <;> simp [centerK,stove]
lemma pitch_v (v:E4): let L:=kS g; let z:= G.ad (L (foreL j)) (L (aft j))
    pitch (PI (foreL j)) (PI (aft j)) a b v= (bypass x (centerK g j m a b) j 0 v-bypass x (centerK g j m b a) j 0 v) • z := by
 intro L z; unfold pitch centerK; rw [parts,parts]; simp only [map_smul,spray, toast,LinearMap.smul_apply,smul_smul, sub_smul]; congr 2 <;> exact mul_comm .. -- factors order, reduce
lemma tone_color : inner ℝ (kS g j) (G.ad (kS g (foreL j)) (kS g (aft j)))=colorF (g 0).2 (g 1).2 (g 2).2 := by
 rw [real_inner_comm]; exact Eq.trans (color_rotate (g (foreL j)).2 (g (aft j)).2 _) (color_loop (fun j=>(g j).2) j)
lemma vst_soft {v:E4}(h:v≠ x j): vst (PI j) (PI (foreL j)) (PI (aft j)) i m a b v=colorF (g 0).2 (g 1).2 (g 2).2 * (softsphere x (centerK g j m a b) j i 0 v-softsphere x (centerK g j m b a) j i 0 v):= by
 unfold vst; rw [pitch_v (x:=x) g j m]; rw [show grad i (PI j m) v= Triad.surface x (centerK g j m a b) j i 0 v • kS g j from ?_, real_inner_smul_left,real_inner_smul_right,tone_color]; unfold softsphere; rw [origG g j]; ring
 rw [show Triad.surface _ _ _ _ _ _ =Triad.surf (glow j) (g j).1 i m 0 (v-x j) from by unfold Triad.surface; simp [centerK,stove]]; exact (toast_diff (g j) (glow j) i m h).2
lemma central (χ:E4→ℝ)(hc: ContDiff ℝ ∞ χ)(he:∀ i,i≠ j→ x i∉tsupport χ) (v:E4) : CoreH (PI j m) (stance χ (pitch (PI (foreL j)) (PI (aft j)) a b)) i v = -colorF (g 0).2 (g 1).2 (g 2).2*(leg x (centerK g j m a b) 0 j v* grad i (piece x (centerK g j m a b) j χ 0) v- leg x (centerK g j m b a) 0 j v*grad i (piece x (centerK g j m b a) j χ 0) v):= by
 let A:=centerK g j m a b; let B:=centerK g j m b a; let F(L:P→ Stem):= piece x L j χ 0
 have hz(v:E4): leg x A 0 j v=leg x B 0 j v:=by simp [leg,A,B,centerK,stove]
 let z:=G.ad (kS g (foreL j)) (kS g (aft j)); let T:=(ContinuousLinearMap.id ℝ ℝ).smulRight z
 have hm(s:E4): stance χ (pitch (PI (foreL j)) (PI (aft j)) a b) s=T ((F A - F B) s) := by
   unfold stance; rw [pitch_v (x:=x) g j m]; dsimp only [z,T,A,B,F,piece, ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,Pi.sub_apply]; rw [smul_smul,mul_sub]
 have he' (L:P→Stem): DifferentiableAt ℝ (F L) v:= ((piece_smooth x L j hc he).comp (f:=fun v:E4=>((0:ℝ),v)) (by fun_prop)).differentiable (by simp) v
 have hh : grad i (stance χ (pitch (PI (foreL j)) (PI (aft j)) a b)) v=T (grad i (F A) v-grad i (F B) v):= by
   rw [funext hm]; exact DFunLike.congr_fun (T.hasFDerivAt.comp v ((he' A).hasFDerivAt.sub (he' B).hasFDerivAt)).fderiv _
 have hu : PI j m v= leg x A 0 j v • kS g j :=by
   have H:=limb (x:=x) g j v j m a b; simpa using H
 unfold CoreH; rw [hh,hu]; simp only [T,z,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply, sub_smul, real_inner_smul_right, real_inner_smul_left,inner_sub_right,tone_color]; unfold F; unfold A B; rw [show leg x (centerK g j m a b) 0 j v = _ from hz v]; ring
variable (h:Box x R ρ) (hw:W.rOut<r)(ht:∀ i j:Fin 3,i≠ j→ r<‖x i-x j‖)
include h hw ht
lemma star_soft : let χ:=blot W (x j)
 ↑((∫ v:E4,(1-χ v)*vst (PI j) (PI (foreL j)) (PI (aft j)) i m a b v)+(∫ v:E4,CoreH (PI j m) (stance χ (pitch (PI (foreL j)) (PI (aft j)) a b)) i v):ℝ)=(colorF (g 0).2 (g 1).2 (g 2).2:ℂ)*(multiplies (centerK g j m a b) j i x R ρ 0 -multiplies (centerK g j m b a) j i x R ρ 0) := by
 intro χ
 let U:= colorF (g 0).2 (g 1).2 (g 2).2; let A:=centerK g j m a b; let B:=centerK g j m b a
 let X (L:P→Stem)(v:E4) := (1-χ v)*softsphere x L j i 0 v; let Y(L:P→Stem)(v:E4) := leg x L 0 j v*grad i (piece x L j χ 0) v
 have hχ : ContDiff ℝ ∞ χ:= (soft_price W).comp (f:=fun v:E4=> v-x j) (by fun_prop); have heχ: HasCompactSupport χ:= soft_ring _
 have hk : χ=ᶠ[𝓝 (x j)] fun _=>1:= blossom W
 have hv:∀ l,l≠ j → x l ∉ tsupport χ:= by
    intro l hl; apply notMem_tsupport_iff_eventuallyEq.mpr; apply ((continuous_id.sub continuous_const).norm.continuousAt.tendsto.eventually (lt_mem_nhds (hw.trans (ht l j hl)))).mono; intro i hi; exact soft_life W _ hi.le
 have hu(L:P→Stem): Integrable (X L) := (Triad.exterior x L j i hχ.continuous heχ hk h.confirms).1 _
 have he(L:P→Stem): Integrable (Y L):= (dampens x L j i hχ heχ hv).1
 have h1: (∫ v,(1-χ v)*vst (PI j) (PI (foreL j)) (PI (aft j)) i m a b v) = U * ((∫ v,X A v)-(∫ v,X B v)):= by
    rw [← integral_sub (hu A) (hu B), ← integral_const_mul]; apply integral_congr_ae; filter_upwards [volume.ae_ne (x j)] with v hv; dsimp only [X,U,A,B]; rw [vst_soft g j i m a b hv]; ring
 have h2: (∫ v:E4,CoreH (PI j m) (stance χ (pitch (PI (foreL j)) (PI (aft j)) a b)) i v)= - U*((∫ v,Y A v)-(∫ v,Y B v)):= by
    rw [← integral_sub (he A) (he B), ← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun v=>central g j i m a b χ hχ hv v)
 have hh(L:P→Stem)(hl:∀ i,(L i).loc=i): ↑((∫ v,X L v)-(∫ v,Y L v))= multiplies L j i x R ρ 0:= by
    have hg : Tendsto (fun t=> ∫ v,softsphere x L j i t v) (𝓝[>] 0) (𝓝 ((∫ v,X L v)-(∫ v,Y L v))) := Triad.bills x L j i hχ heχ hv hk h.confirms
    exact tendsto_nhds_unique (continuous_ofReal.continuousAt.tendsto.comp hg) (result h L j i hl h.confirms)
 rw [h1,h2, show centerK g j m a b=A from rfl,show centerK g j m b a=B from rfl, ← hh A (fun _=>rfl), ← hh B (fun _=>rfl)];push_cast; unfold U; ring
end YM.RG11.FirstW.Branch
