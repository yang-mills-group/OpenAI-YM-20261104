import YM.OPE.Compatible.Chain.Zing
/-!
# Ledger of arbitrary alpha cash (beta normalization). subtract evaluated constants. Analytic data may always be taken Borel globally.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script
open PertExtension Series Asymptotics
variable {i:ℕ}{l:ℝ}{B:Sponsor G}{Q:Seasons B}
local notation "Lf" => Tested.germ
-- exact functional at all levels and at branch volumes
variable (H:Even n.val) (A:Alps B Q i l)
local notation "TK" => Libra.Keys G (Limb H)
def mural (u:TK):ℝ:= swornV A.clip A.live (cloak H u)/4
def gilt (u:TK):ℝ:= swornY A.live (cloak H u)/4
def tintT (b:ℝ)(u:TK):ℝ:= Real.exp (-b*mural H A u-gilt H A u)
lemma muralD : ContDiffAt ℝ ω (mural H A) 0:= ((show ContDiffAt ℝ ω _ (cloak H (0:TK)) from (cloak H).map_zero.symm ▸ (A.fullK 1).plot n).comp 0 (cloak H).contDiff.contDiffAt).div_const 4
lemma tintD (b:ℝ): ContDiffAt ℝ ω (tintT H A b) 0:= (((muralD H A).const_smul (-b)).sub (((show ContDiffAt ℝ ω (swornY A.live) (cloak H (0:TK)) from (cloak H).map_zero.symm ▸ (A.fullL 1).plot n).comp 0 (cloak H).contDiff.contDiffAt).div_const 4)).exp
section
omit H A
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E]{f:E→ℝ}
lemma arcShape (hf:ContDiffAt ℝ ω f 0):∃ g:E→ℝ,Measurable g ∧ g =ᶠ[𝓝 0] f:=by
     obtain ⟨s,h,hx,hF⟩:= hf.contDiffOn' (m:=0) (by simp) (by simp); simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hF; exact ⟨s.indicator f, ContinuousOn.measurable_piecewise hF.continuousOn continuous_const.continuousOn h.measurableSet, (h.mem_nhds hx)|> fun h=>Filter.mem_of_superset h fun i hi=>by simp [hi]⟩
end
lemma muralG (x y:TK)(g:Libra.Tile G (Node H))(h:(Pond H).dress g (put x)=put y): mural H A x=mural H A y ∧ gilt H A x=gilt H A y:=by
    have hp: Lattice.gauge (fun i=>g (crumb H i)) (represent (cloak H x))=represent (cloak H y):=by
        rw [cloak_e,cloak_e,←h,show (Pond H).dress g _=energyG H g _ from rfl,coat_gauge]
    unfold mural gilt swornV swornY; dsimp only [Function.comp_apply]; rw [← hp]; simp only [(A.fullK 0).stand n _ (represent _), (A.fullL 0).stand n _ (represent _)]; simp
lemma tracksW (b:ℝ){f w:TK→ℝ}(h:f =ᶠ[𝓝 0] fun x=> mural H A x-mural H A 0)(hw:w =ᶠ[𝓝 0] tintT H A b): (Pond H).Walks f w:=by
     refine ⟨((muralD H A).of_le le_top|>.sub contDiffAt_const |>.congr_of_eventuallyEq h), ((tintD H A b).of_le le_top |>.congr_of_eventuallyEq hw),fun {x y s} g=>?_,fun {x y s} g=>?_⟩
     · refine (isBigO_zero _ Lf).congr' ?_ Filter.EventuallyEq.rfl; have he:Tendsto x Lf (𝓝 0):= g.gx ▸ g.hX.continuousAt.continuousWithinAt; have hv:Tendsto y Lf (𝓝 0):= g.gy ▸ g.hY.continuousAt.continuousWithinAt; filter_upwards [he.eventually h,hv.eventually h,g.law.filter_mono nhdsWithin_le_nhds] with t ha ht hh; change f (x t)=_ at ha; rw [ha, ht]; rw [(muralG H A _ _ _ hh).1]; ring -- type track
     refine (isBigO_zero _ Lf).congr' ?_ Filter.EventuallyEq.rfl; have he:Tendsto x Lf (𝓝 0):= g.gx ▸ g.hX.continuousAt.continuousWithinAt; have hv:Tendsto y Lf (𝓝 0):= g.gy ▸ g.hY.continuousAt.continuousWithinAt; filter_upwards [he.eventually hw,hv.eventually hw,g.law.filter_mono nhdsWithin_le_nhds] with t ha ht hh; rw [ha,ht,tintT,tintT,(muralG H A _ _ _ hh).1,(muralG H A _ _ _ hh).2,sub_self]
end YM.OPE.Cascade
