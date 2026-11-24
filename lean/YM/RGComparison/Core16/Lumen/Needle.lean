import YM.RGComparison.Core16.Lumen.Spacing
/-!
# First task-step bootstrap into a Fk/A seam estimate. Z step gravity
Use hats, mask, actual sector travels. Scope currently one-step top startup; all calls
pre-era. Reserve use after being paid by D_ψ. Includes exact logTag dependence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Gravity
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals Matrix
open PertExtension PertExtension.Series Tested Radial Therm
open Stage Finset Planet
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}(P:Planet X S ι k T) (i:Wire G ι)

def path (a:k): Stuff G ι (Bool ⊕ D):= Sum.elim (fun j=> if j then .inr (P.ray a) else .inl i.1) (fun j=>(P.stem a j).elim (.inr 0) Sum.inl)

def incision (G:Gauge)(D:Type)[Fintype D] : ((Bool⊕D)→ G.Color)→L[ℝ] Point G D:=
    (ContinuousLinearMap.proj (.inl true)).prod (ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (.inr i)))
def recipe (X:Shelf G A D)(i:A×(D→Bool)× G.ColorIndex)(y:(Bool⊕D)→ G.Color):ℝ:= (fderiv ℝ (X.U i.1) (incision G D y)) (press i.2.1 (roll i.2.2 (G.mat (launch (y (.inl false))))))

def weight (b:ContDiffBump (0:ℝ))(a:k) (g:ℝ):= P.dark b i * P.drizzle i a g

variable {P i}{k':Wire G ι}(b:ContDiffBump (0:ℝ))
-- Paired approach at this tokenizer; `P.O not continuous globally` no reliance.
lemma fatigue (Y:Good X)(j:A×(D→Bool)× G.ColorIndex) : ContDiffAt ℝ ω (recipe X j) 0:=by
    let p:= incision G D
    let h:= (higher Y j.1).fderiv_right (by simp : (ω:WithTop ℕ∞)+1 ≤ω)
    let F: Point G D→ Point G D→L[ℝ] ℝ:= fderiv ℝ (X.U j.1); have H : ContDiffAt ℝ ω (F ∘ p) 0:= (map_zero p ▸ h : ContDiffAt ℝ ω F (p 0)).comp (f:=p) _ p.contDiff.contDiffAt
    exact H.clm_apply ((press j.2.1).contDiff.contDiffAt.comp (𝕜:=ℝ) (0:Bool⊕ D→ G.Color) ((roll_hot j.2.2).contDiffAt.comp (𝕜:=ℝ) (0:Bool⊕D→ G.Color) (launch_data.comp (0:Bool ⊕ D→ G.Color) (f:=fun y=> y (.inl false)) (contDiff_apply ℝ _ _).contDiffAt))) -- meta

lemma gravity_jet (Y:Good X)(j : A × (D→Bool)× G.ColorIndex)(y:(Bool⊕D)→G.Color) :
    jet (recipe X j) 1 y=shelfH X j.1 (incision G D y) (press j.2.1 (colors G j.2.2)):=by
    let K:=j.1; let b:=(incision G D); let n (y:(Bool⊕D)→G.Color) := press j.2.1 (roll j.2.2 (G.mat (launch (y (.inl false)))))
    have he: ContDiffAt ℝ ω (fderiv ℝ (X.U K)) (b 0):= by rw [map_zero]; exact (higher Y j.1).fderiv_right le_top
    let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bool⊕D=>G.Color) (.inl false)
    have hz: ContDiffAt ℝ ω n 0:= ((press j.2.1).contDiff.contDiffAt.comp (𝕜:=ℝ) (0:Bool⊕ D→ G.Color) ((roll_hot j.2.2).contDiffAt.comp _ (show ContDiffAt ℝ ω (fun (x:Bool⊕D→ G.Color)=>G.mat (launch (L x))) (0:Bool⊕ D→G.Color) from ((map_zero L ▸ (show ContDiffAt ℝ ω (fun x=> G.mat (launch x)) 0 from launch_data)) : ContDiffAt ℝ ω (fun x=> G.mat (launch x)) (L (0:Bool⊕ D→ G.Color))).comp (f:=L) (0:Bool⊕ D→ G.Color) L.contDiff.contDiffAt)))
    have h:= ((he.differentiableAt (by simp)).hasFDerivAt.comp (f:=b) _ b.hasFDerivAt).clm_apply (hz.differentiableAt (by simp)|>.hasFDerivAt)
    let F:Point G D→ Point G D→L[ℝ] ℝ:= fderiv ℝ (X.U j.1)
    unfold jet; rw [iteratedFDeriv_one_apply]
    change (↑(_):ℝ)⁻¹ *((fderiv ℝ (fun y=> (F ∘ b) y (n y)) 0) y)=_
    rw [h.fderiv]; simp only [map_zero,K, Function.comp_apply, (Y.first _).fderiv, show n 0= _ from (congr_arg (fun v=> press j.2.1 v) (show roll j.2.2 (G.mat (launch (0:G.Color)))= _ from by rw [launch_zero,G.mat_one,roll_one])), _root_.add_apply,ContinuousLinearMap.comp_apply] -- simplify
    simp [b,shelfH]

variable (H:P.Steady){g:ℝ}(hg:amen X g){a:k}(ha:a∈ P.within i.1)
include H
include ha in
lemma preach : celery (path P i a) (P.heat i.1) X.Q:= by
   intro j; rcases j with (_|_)|p
   · exact P.loc_heat _
   · exact H.priced a
   unfold path; dsimp only [Sum.elim_inr]; cases he:P.stem a p with
   | none=> exact (le_of_eq (by simp) : ‖(0:G.Color)‖ ≤ (0:ℝ)).trans H.prices.thick.1.le
   | some j=> exact P.soil_heat ha (H.thread a p j he)

include hg
lemma loads_all (a:k)(x:Sky G ι): ‖P.load a g x‖ ≤ X.R+2:=by
    unfold Planet.load; rw [Prod.norm_def,norm_smul]; refine max_le ?_ ?_
    · rw [Real.norm_of_nonneg hg.1]; exact (mul_le_mul hg.2 (H.priced a) (norm_nonneg _) H.prices.thick.2.1.le).trans ((H.prices.thick.2.2.trans (by linarith)).le)
    have hX:= H.prices.positive
    rw [pi_norm_le_iff_of_nonneg (by positivity : 0≤ X.R+2)]; intro i; change ‖portrait _ _ i‖ ≤ _ ; unfold portrait; cases he:P.stem a i with
    | none=> simp; linarith
    | some i=> exact ((G.curvature_norm _).trans (G.chord_le_two ..)).trans (le_add_of_nonneg_left hX.le)

omit hg H [Fintype ι] [Fintype k] [Fintype T] in
lemma trick (hg:0<g)(x:Sky G ι) : incision G D (g • book (path P i a) g x)=P.load a g x ∧ g • book (path P i a) g x (.inl false)=G.curvature (x i.1) := by
   refine ⟨Prod.ext (by rfl) (funext fun j=>?_), smul_inv_smul₀ hg.ne' _⟩
   change g • book (path P i a) g x (.inr j)=portrait (P.stem a) _ j
   unfold portrait book path; dsimp only [Sum.elim_inr]; cases he:P.stem a j with
   | none=> simp
   | some i=> exact smul_inv_smul₀ hg.ne' _

omit hg in
lemma colouring (b:ContDiffBump (0:ℝ)) (hb:Dust b X.δ)(hk:0<g)(x:Sky G ι)(hx:crisp (X.δ/2) (P.heat i.1) x):
    weight P i b a g x=recipe X (P.glyph a,P.hint a i.1, i.2) (g • book (path P i a) g x):=by
   let v:=incision G D
   obtain ⟨hw,hA⟩:=trick (P:=P) (i:=i) (a:=a) hk x
   have hp:= live i hb hx
   unfold recipe; rw [hw,Pi.smul_apply,hA,H.prices.reenter (x i.1) ((hx i.1 (P.loc_heat i.1)).trans (by linarith [H.prices.extent.1]))]; unfold weight; rw [Pi.mul_apply,hp.1,one_mul]; rfl
omit H hg

-- pack prices Survey count with Exp/L portability

def patchN (Y:Prices):ℕ:= ballCost (2*Y.b) * Y.K
include H in
lemma shelter : (P.heat k'.1).card ≤ patchN X.sector:= price_cover (loc:=P.loc) ((H.tickets 0 ⟨le_refl _,H.prices.thick.2.1.le⟩).core) _ _
variable [Fintype A]
theorem need_cost (Y:Good X):∃ C:ℝ,0≤C ∧ ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(n:Side)(P:Planet X n ι k T) (_h:P.Steady)(b:ContDiffBump (0:ℝ))(_hb:Dust b X.δ)(i:Wire G ι) (a:k), a∈ P.within i.1→ Visible X (recipe X (P.glyph a,P.hint a i.1,i.2)) (weight P i b a) (path P i a) (patchN X.sector) C:=by
    choose E hE using fun j:G.ColorIndex=> (isCompact_univ (X:=G.El)).exists_bound_of_continuousOn (((roll_hot j).continuous.comp G.continuous_mat).continuousOn)
    choose D hD using fun i=> (isCompact_closedBall (0:Point G D) (X.R+2)).exists_bound_of_continuousOn ((Y.smooth i).continuous_fderiv (by simp)|>.continuousOn)
    let w:=∑ j:G.ColorIndex, |E j|; let q:=∑ i:A,|D i|; have hw:0≤ w:=sum_nonneg fun _ _=> abs_nonneg _; have hq:0≤ q:=sum_nonneg fun _ _=> abs_nonneg _
    refine ⟨q*w,by positivity,fun ι k T _ _ _ n P hP b hb i a ha=> ?_⟩
    let V:=P.heat i.1; refine ⟨fun g hg=>(P.whirl b i).1.mul (havenreal (drizzle_cont i hP g a)),fun g hg x=>?_,V, shelter hP, preach hP (a:=a) (i:=i) ha,fun g hg hh x hx=> colouring hP b hb hh x hx⟩
    have he:E i.2 ≤ w:=(le_abs_self _).trans (single_le_sum (f:=fun j=>|E j|) (fun _ _=>abs_nonneg _) (mem_univ _)); have hd:D (P.glyph a) ≤ q:=(le_abs_self _).trans (single_le_sum (f:=fun i=>|D i|) (fun _ _=>abs_nonneg _) (mem_univ _))
    have hz : |P.drizzle i a g x| ≤ q*w:=by
        apply (fderiv ℝ (X.U (P.glyph a)) (P.load a g x)).le_of_opNorm_le_of_le ((hD (P.glyph a) (P.load a g x) (mem_closedBall_zero_iff.mpr (loads_all hP hg a x))).trans hd) ((press_cost ..).trans ((hE i.2 (x i.1) (Set.mem_univ _)).trans he))
    rw [weight, Pi.mul_apply,abs_mul, abs_of_nonneg (P.dark_grip b i x|>.1)]; exact (mul_le_of_le_one_left (abs_nonneg _) (P.dark_grip ..|>.2)).trans hz
end YM.RGComparison.Core16.Lumen.Gravity
