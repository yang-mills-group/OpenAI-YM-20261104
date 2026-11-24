import YM.Contacts.Procession.Public
/-! # Pivots, aperture matrix before Wick normalization. Include one Mark, no source align bound. -/
noncomputable section
namespace YM.Contacts.Procession.Cartons
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Shuttle Tide
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
open Morning Mediator Next.Foundations
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 90000
set_option autoImplicit false
variable {G:Gauge}{X Y: Type}{m:Side}{F:Cohort G}{d k h u n:ℕ}(B: Labels.Frame G d)
-- read on entire Mark.App.No power prices assumed.
open Planned.PrimaryIntegral295 WardBin Push.Local Catch Welcome Lumen Larch Sun
-- geometry: d same Bitcoin.Label. s.Oa.Length native. Depth Π and primal. Reads in boost-old or any canonical own boost-new once a record is known.
local notation "axis!" => (d*(d+1))
-- per charge ℓ digit (can also use on boosted vacuum kernel valued ℓ)
variable {i l p:ℕ}{V:bore G}
abbrev velum (X:Cohort G)(v:B.Index):ℝ:= (exhibit B (panel X d axis! d) v).re
private lemma realies {z:ℂ} (h:star z=z) : (z.re:ℂ)=z:= by
   apply Complex.ext; rfl; have he:= congr_arg Complex.im h; change -z.im=z.im at he; simp; linarith
lemma charter {B:Labels.Frame G d}{X:Cohort G}(h:Tags X) (v:B.Index): ((velum B X v):ℂ)=exhibit B (panel X d axis! d) v:=realies (congr_fun ((gauges B h le_rfl le_rfl).clarity) v)
-- canvas vac preparation on 0.Snap. If no rank through k -> derivative row at k vanishes (regardless of higher ranks).
def costume (d u:ℕ): Snap G d→Ship G u:= rain G d u ∘ plank G d
lemma costume_diff (G:Gauge) (d u:ℕ):ContDiffAt ℝ ω (costume (G:=G) d u) 0:= ContDiffAt.comp _ (by rw [(plank G d).map_zero]; exact germ_rain ..) (plank G d).contDiff.contDiffAt
@[simp] lemma costume_zero (G:Gauge) : costume (G:=G) d u 0=0:= by rw [costume,Function.comp_apply,map_zero]; exact rain_base ..
lemma torn {X:Cohort G}(h:k≤ n)(hh:∀ i≤k,X i=0) : Tensor.coeff (cotton (panel X d u n)) k 0=0:= by
    let f:= cotton (panel X d u n); let p:=panel X d u n; let ρ:=costume (G:=G) d u; let A:= rows X u n; have he i (hi:i ≤ k) : iteratedFDeriv ℝ i A (ρ 0)=0:=by -- use serialization but X not Felt. higher τ effects none
       let s:= Finset.range (n+1); let P j := Tensor.diagonal (sheet j (X j) (lens G u)); have hs j: ContDiffAt ℝ ω (P j) 0:= (diag_smooth ..).contDiffAt; let Q:= Tensor.coeff A i 0; have hA:Tensor.Sym Q:= Tensor.coeff_symm ((rows_diff ..).contDiffAt.of_le le_top)
       have hz:Q=0:= by
           refine Tensor.ext_diag _ _ hA (fun _ _=> rfl) (funext fun v=>?_); change PertExtension.Series.Radial.jet A i v=0; unfold A rows; rw [Ion.loan_sum]; swap; · exact fun i _=>(hs i).analyticAt
           refine sum_eq_zero (fun b hb=>?_); rw [Milling.radiant (hs b).analyticAt b i (fun x t=> Tensor.homogeneous _ x t) v]; split
           next h=>
              subst b; unfold P; rw [hh i hi]; have hx (Y:Fin i→Node (Dye G)) : blanket i 0 (Tide.lens G u) Y=0:= (by ext; simp [blanket]);
              simp [Tensor.diagonal,sheet,hx]
           rfl
       unfold Q Tensor.coeff at hz; rw [smul_eq_zero] at hz; rw [show ρ 0=_ from costume_zero _]
       exact hz.resolve_left (by positivity)
    have ht: iteratedFDeriv ℝ k p 0=0:=by
       change iteratedFDeriv ℝ k (A∘ρ) 0=0; ext v; rw [iteratedFDeriv_comp (rows_diff ..|>.contDiffAt) (costume_diff G d u) (show (k:WithTop ℕ∞)≤ω from le_top),FormalMultilinearSeries.taylorComp,_root_.sum_apply]; refine sum_eq_zero fun i _=>?_; change (iteratedFDeriv ℝ i.length A (ρ 0)) _=0; rw [he _ i.length_le]; rfl
    unfold cotton Tensor.coeff; rw [Complex.ofRealCLM.iteratedFDeriv_comp_left (smooth_panel ..) (show (k:WithTop ℕ∞)≤ω from le_top),ht]; ext v; simp
lemma vela_silent {B:Labels.Frame G d}{X:Cohort G}(h:Tags X)(v:B.Index)(hv:∀ j≤(B.grades v).2,X j=0): velum B X v=0:=by
   let E:=exhibit B (panel X d axis! d); have H:= gauges B h le_rfl le_rfl; let Q:=gradePart (B.grades v) (B.coords.symm E); have hp:Q=0:= by
       have hx:= H.detects v ((smooth_panel X d axis! d).of_le le_top); have ht:=torn (h:=Film.second_fits B v) hv (d:=d) (u:=axis!); rw [ht] at hx; apply Subtype.ext; change (gradePart _ (B.coords.symm E)).val=0; exact hx.trans (by simp [WardBin.tile]); -- names
   apply Complex.ofReal_injective; rw [charter h,Complex.ofReal_zero]; change E v=0; calc
     _=B.coords (B.coords.symm E) v:=congr_fun (B.coords.apply_symm_apply E).symm v
     _=B.coords Q v:= Film.costs_only ..
     _= _:=by rw [hp,map_zero]; rfl
private lemma whisk {X:Type}(F:House X)(p l i:ℕ)(h:l+i<p+4): coil F p l i=0:=by unfold coil Resetter.dazzle shiftA; split; split; unfold Catch.cap at *; omega; rfl; rfl
-- support in i output rank. Π order formula.
def fill (p:ℕ)(V:bore G)(i:ℕ)(v:B.Index) : ℝ:= if (B.grades v).2≤ p+i then velum B (coil V p (p+4+i-(B.grades v).2)) v else 0
lemma fueled {B:Labels.Frame G d}{V:bore G} (h:Mount V p)(y:Dye G){s:ℝ≥0}(hs:0<s){U: TableFee}(hp:Price V y s U)(l:ℕ)(v:B.Index): velum B (coil V p l) v = if p+4 ≤ l+(B.grades v).2 ∧ 4 ≤ l then fill B p V (l+(B.grades v).2-(p+4)) v else 0:= by
   let k:=(B.grades v).2; have he:= Catch.coil_tags h hp hs l; split
   next h' => unfold fill; rw [if_pos (by omega)]; congr! 2; omega -- maybe
   next h' => refine vela_silent he v (fun j hj=>?_); rcases not_and_or.mp h' with h'|h'; exact whisk _ _ _ _ (by omega); unfold coil Resetter.dazzle shiftA; split; split; rename_i h₂ h₃; exact h.incarnate.thin _ _ (by unfold Catch.cap at *; omega); rfl; rfl
end YM.Contacts.Procession.Cartons
