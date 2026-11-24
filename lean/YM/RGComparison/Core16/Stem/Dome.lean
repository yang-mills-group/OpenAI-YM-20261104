import YM.RGComparison.Core16.Lumen.Project
import YM.RGComparison.Core16.Laplace

/-!
# Identifying the uniform-pressure estimator with full Gaussian FK/A stencil

Primitive tier full connected output normalized to conditional Markov at V=exp(g*u). This is
local input at physical TOP seam; real V values here in that germ, no capture or winding adaptor
to the IR regulator yet. Keep Haar (counting or orthonormal real product volume with chart billing)
and β signs. Deep precision estimate at this seam not inferring YM running law.
Price building cost graphs before Θ estimator required as previously. This file removes η
at projection if budget run at given Λ planner.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Fk
open Function Filter Set Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open PertExtension PertExtension.Series Tested Radial Therm
open Planet
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side} {ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}(P:Planet X S ι k T)
abbrev Panel (G:Gauge)(ι:Type):=ι→ G.Color
abbrev Door (G:Gauge)(ι:Type):= ℝ × Panel G ι

def spread (Y : Panel G ι): Sky G ι:= G.lieExp ∘ Y
def postage (x:Door G ι)(a:k):=X.U (P.glyph a) (P.load a x.1 (spread x.2))
def lapse (x:Door G ι):=∑ a,postage P x a
-- fake external positive quadratic makes Radial positivity on this presentation; restore `exp(1)`
def rise (x:Door G ι) := x.1^2 + lapse P x
abbrev deck : Set (Sky G ι):={x| crisp X.δ Finset.univ x}
variable {P}(H:P.Steady)
omit [Fintype T] [Fintype k] [Fintype ι] [Fintype D] in
lemma null (a:k) : P.load a 0 (spread 0)=0:=by refine Prod.ext ?_ (funext fun i=>?_); change (0:ℝ) • _ = 0; simp; change portrait (P.stem a) _ i=0; unfold portrait; cases he:P.stem a i with
   | none=> rfl
   | some j=> simp [spread]
include H
lemma wages (x : Door G ι) (hx: amen X x.1) (hk: spread x.2∈deck (X:=X)) (t:T): rise P x= x.1^2+(P.F x.1).action t (spread x.2):=by
    exact congr_arg (x.1^2+·) (Finset.sum_congr rfl fun i _=> (H.pay _ hx i _ t (crisp_negligible _ _ le_rfl (Finset.subset_univ _) hk)).symm)
omit H [Fintype k] [Fintype T] in
private lemma reserve (a:k) : ContDiff ℝ ω (fun x:Door G ι=> P.load a x.1 (spread x.2)) := by
   refine (contDiff_fst.smul contDiff_const).prodMk (contDiff_pi.mpr fun i=> ?_); unfold portrait; simp only [spread,comp_apply]; rcases he:P.stem a i with _|j; exact contDiff_const
   exact turn_hot.comp ((contDiff_apply ℝ _ _).comp (f:=Prod.snd) contDiff_snd)
lemma bump_hot : ContDiffAt ℝ ω (rise P) 0 := by
   unfold rise Fk.lapse Fk.postage; exact (contDiffAt_fst.pow 2).add (ContDiffAt.sum fun j _=> (show ContDiffAt ℝ ω _ (P.load j 0 (spread 0)) from (null (P:=P) j).symm ▸ (higher H.prices (P.glyph j))).comp (f:=fun y:Door G ι=> P.load j y.1 (spread y.2)) _ (reserve (P:=P) j|>.contDiffAt))
lemma sturdy : Stationary (rise P):=by
   have hx:rise P 0=0:=by change (0:ℝ)^2+(∑ a,X.U (P.glyph a) (P.load a 0 (spread 0)))=0; simp_rw [Fk.null,H.prices.zeroth]; simp
   have he (a:k):HasFDerivAt (fun x:Door G ι=> postage P x a) (0:Door G ι →L[ℝ] ℝ) 0:=by
       let f (x : Door G ι):= P.load a x.1 (spread x.2); have h:f 0=0:=null a; have he := (reserve (P:=P) a).contDiffAt (x:=0); change ContDiffAt ℝ ω f _ at he
       have hx:HasFDerivAt (X.U (P.glyph a)) (0:Point G D→L[ℝ] ℝ) (f 0):= h.symm ▸ H.prices.first _; exact (hx.comp 0 (he.differentiableAt (by simp)|>.hasFDerivAt)).congr_fderiv (by simp) -- name
   have hT: HasFDerivAt (rise P) (0:Door G ι→L[ℝ] ℝ) 0:= by
       convert! (((hasFDerivAt_fst (𝕜:=ℝ) (p:=(0:Door G ι))).pow 2).add (HasFDerivAt.fun_sum (u:=Finset.univ) (fun a _=> he a))) using 1; simp
   refine ⟨(bump_hot H).of_le le_top,hx,fun x=>?_⟩; rw [←score_jet,score_one,hT.fderiv]; rfl
private lemma limit (Y:Door G ι): Tendsto (fun t:ℝ=> t⁻¹ ^ 2*rise P (t • Y)) Tested.germ (𝓝 (jet (rise P) 2 Y)):= by
     refine ((directions ((bump_hot H).of_le le_top) Y).shift (w:=2) ?_).tendsto_first -- parameter k?
     intro k hk; interval_cases k
     · exact (jet_zero ..).trans (Fk.sturdy H).base0
     exact (Fk.sturdy H).base1 _

private lemma ascent (x:Door G ι)(hx:amen X x.1)(hw:spread x.2∈deck (X:=X)) : x.1^2 ≤ rise P x ∧ ∀ i:ι,G.chord (spread x.2 i)^2 ≤ X.sector.D * rise P x := by
    let V:= spread x.2; let g:=x.1; let U:=P.F g; have he:=H.tickets _ hx
    have hX:=show 0 < ∑ a,U.choices a V from (show ∑ a,U.choices a V=1 from he.normalized _) ▸ zero_lt_one
    obtain ⟨i,-,hi⟩:= (Finset.sum_pos_iff_of_nonneg (fun j _=> he.pos V j)).mp hX
    rw [wages H x hx hw i]; have hj:= he.generates V i
    refine ⟨le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>hj _), fun j=> (he.min _ i j hi).trans ?_⟩; gcongr; exact X.sector.D_pos.le; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>hj _)

lemma prepared : ∃ c>0,∀ x:Door G ι,c*‖x‖^2 ≤ jet (rise P) 2 x:=by
   apply quadratic_min
   have Hq: Tendsto (spread (G:=G) (ι:=ι)) (𝓝 0) (𝓝 1):= tendsto_pi_nhds.mpr fun i=> by simpa [spread] using! ((show Continuous (fun u:Panel G ι=> G.lieExp (u i)) from by fun_prop).tendsto 0)
   let W := deck (G:=G) (X:=X) (ι:=ι); have hM:=Hq.eventually ((crisp_open ..).mem_nhds (show (1:Sky G ι)∈W from fun i _=> by simp [H.prices.extent.1]))
   have hz (x:Door G ι)(hx:0≤x.1)(hy:x≠0):0<jet (rise P) 2 x:=by
       have hc : Tendsto (fun r:ℝ=>r • x) Tested.germ (𝓝 0):=by simpa only [zero_smul] using! ((show Continuous (fun r:ℝ=>r • x) by fun_prop).tendsto 0 |>.mono_left nhdsWithin_le_nhds)
       let f (t:ℝ) : Prop:= amen X ((t • x).1) ∧ spread (t • x).2∈W
       have hp: ∀ᶠ t:ℝ in Tested.germ, f t:=by
           filter_upwards [Tested.eventually_pos,hc.eventually (((continuous_fst.tendsto (0:Door G ι)).eventually (gt_mem_nhds H.prices.thick.2.1)).and ((continuous_snd.tendsto (0:Door G ι)).eventually hM))] with t ht he
           exact ⟨⟨mul_nonneg ht.le hx,le_of_lt (show _ <X.knot from he.1)⟩, he.2⟩
       by_cases hw:0<x.1
       · refine lt_of_lt_of_le (pow_pos hw 2) (ge_of_tendsto (limit H x) ?_)
         filter_upwards [hp,Tested.eventually_pos] with i (hi:f i) h
         exact (mul_le_mul_of_nonneg_left (ascent H (i • x) hi.1 hi.2|>.1) (sq_nonneg i⁻¹)).trans' (show x.1^2 ≤ i⁻¹^2*(i*x.1)^2 by field_simp; norm_num)
       obtain ⟨i,hi⟩:∃ i:ι,x.2 i ≠ 0:=by by_contra! h; exact hy (Prod.ext (le_antisymm (not_lt.mp hw) hx) (funext h))
       suffices he : ‖x.2 i‖^2 ≤ X.sector.D * jet (rise P) 2 x by exact pos_of_mul_pos_right ((pow_pos (norm_pos_iff.mpr hi) 2).trans_le he) X.sector.D_pos.le
       have hl : Tendsto (fun t:ℝ=> ‖t‖⁻¹ * G.chord (spread (t • x).2 i)) Tested.germ (𝓝 ‖x.2 i‖):= by
            let f:= x.2 i; have he : Tendsto _ (𝓝[≠] (0:ℝ)) (𝓝 ‖f‖):= Work.F01.chord_limit (v:=f) (U:= fun t=> G.lieExp (t • f)) (by simp) ?_
            · exact he.mono_left (nhdsWithin_mono _ fun v hv=> ne_of_gt hv)
            have h : HasDerivAt (fun t:ℝ=> t • f) f 0:=by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const f
            exact ((show HasFDerivAt (fun x=> G.mat (G.lieExp x)) (G.colorMat.toContinuousLinearMap) ((0:ℝ) • f) from by rw [zero_smul]; exact G.expDiff_zero)).comp_hasDerivAt 0 h
       refine le_of_tendsto_of_tendsto (hl.pow 2) ((limit H x).const_mul _) ?_; filter_upwards [Tested.eventually_pos,hp] with t ht (h:f t); have hp := (ascent H _ h.1 h.2).2 i; rwa [Real.norm_of_nonneg ht.le,mul_pow, mul_left_comm X.sector.D, mul_le_mul_iff_right₀ (by positivity : 0<t⁻¹^2)]
   intro x hx; by_cases H₀:0 ≤ x.1
   · exact hz x H₀ hx
   have H₁ := hz (-x) (by rw [Prod.fst_neg]; exact neg_nonneg.mpr (le_of_not_ge H₀)) (neg_ne_zero.mpr hx); rw [← neg_one_smul ℝ x,Radial.jet_smul] at H₁; norm_num at H₁; exact H₁
end YM.RGComparison.Core16.Lumen.Fk
