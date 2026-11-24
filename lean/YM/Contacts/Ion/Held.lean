import YM.Contacts.Ion.Linear
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
open MeasureTheory MeasureTheory.Measure Metric PertExtension.Chart
open scoped ENNReal
variable {R:ChartRatio G} (h:LocalRatio R)
local notation "ξ" => G.Color
local notation "θU"=> (Metric.ball (0:ξ) R.radius)
local notation "κx"=> (MeasureTheory.volume.restrict θU)
local notation "F"=> (fun x=> ENNReal.ofReal (R.scale*R.J x))
local notation "Θ"=> G.lieExp
include h
-- full patch local Jacobian at mirrored chart angles
lemma feeBill (A:Set ξ)(he:MeasurableSet A): ∫⁻ x in A,F x ∂κx = G.probHaar (Θ '' (A ∩ θU)):= by
    let p := Θ '' (A∩θU); let q:= Θ '' θU; have ht:= (he.inter measurableSet_ball).image_of_continuousOn_injOn G.lieExp_cont.continuousOn (h.inject.mono Set.inter_subset_right); -- arg order
    have hh : Θ ⁻¹' p ∩ θU=A∩θU:= by ext x; constructor; rintro ⟨⟨y,⟨hy,hU⟩,hh⟩,hx⟩; exact ⟨(h.inject hU hx hh) ▸ hy,hx⟩; exact fun hx=>⟨⟨x,hx,rfl⟩,hx.2⟩
    have hv:= G.lieExp_cont.measurable ht
    calc
       _ = (((κx).withDensity F).map Θ) p:= by rw [Measure.map_apply G.lieExp_cont.measurable ht,withDensity_apply F hv,Measure.restrict_restrict he,Measure.restrict_restrict hv,hh]
       _ = _:= by rw [h.actual,Measure.restrict_apply ht]; exact congr_arg G.probHaar (Set.inter_eq_left.mpr (Set.image_mono Set.inter_subset_right)) -- err
local notation "L" => (Neg.neg : ξ→ ξ)
local notation "J" => (Inv.inv : G.El→G.El)
lemma present_fee (A:Set ξ)(he:MeasurableSet A): ∫⁻ x in A,F x ∂κx=∫⁻ x in A,(F ∘ L) x ∂κx:= by
    have hu : L ⁻¹' θU=θU:= by ext x; simp [Metric.mem_ball]
    let P:= L ⁻¹' A; let v:= Θ '' (P∩θU); let p:= Θ '' (A∩θU); have hP:MeasurableSet P:=measurable_neg he; have hv: v= J ⁻¹' p:= by ext x; constructor; rintro ⟨y,hy,rfl⟩; exact ⟨-y,⟨hy.1,show L y ∈ θU from (Set.ext_iff.mp hu _) |>.mpr hy.2⟩, Work.F03.exp_neg_color y⟩; rintro ⟨y,hy,hh⟩; exact ⟨-y,⟨(show -(-y)∈A by simpa using hy.1),show L y∈θU from ((Set.ext_iff.mp hu _) |>.mpr hy.2)⟩,(Work.F03.exp_neg_color y).trans ((congr_arg Inv.inv hh).trans (inv_inv _))⟩
    have hg: MeasurableEmbedding L:=(Homeomorph.neg _).measurableEmbedding
    have hx : MeasurePreserving L κx κx:= by simpa [hu] using ((Measure.measurePreserving_neg (MeasureTheory.volume:Measure ξ)).restrict_preimage_emb hg θU)
    have hk:L ⁻¹' P = A:= by ext x; change -(-x) ∈ A ↔ _; rw [neg_neg]
    have hl:= hx.setLIntegral_comp_preimage_emb hg F P; rw [hk] at hl; suffices hh:G.probHaar p=G.probHaar v from ((feeBill h A he).trans (hh.trans ((feeBill h P hP).symm.trans hl.symm))); rw [hv]; exact (G.preserve_inv.measure_preimage_emb (Homeomorph.inv G.El).measurableEmbedding p).symm
lemma even_fee : Set.EqOn F (F ∘ L) θU := by
   let P:=F; have hc: ContinuousOn P θU := ENNReal.continuous_ofReal.continuousOn.comp (continuousOn_const.mul (fun x hx=>(h.germ x hx).continuousAt.continuousWithinAt)) (Set.mapsTo_univ ..); -- comp inference
   have hv : Measurable P:= (h.borel.const_mul _).ennreal_ofReal; refine eqOn_open_of_ae_eq (μ:=MeasureTheory.volume) (?_) isOpen_ball hc (hc.comp continuous_neg.continuousOn (fun x hx=>by simpa [Metric.mem_ball] using hx))
   apply (withDensity_eq_iff_of_sigmaFinite hv.aemeasurable (hv.comp measurable_neg).aemeasurable).1; ext A he; rw [withDensity_apply _ he,withDensity_apply _ he]; exact present_fee h A he
lemma collected (x:ξ)(ht:x∈θU): fee R x=fee R (-x):= by
   unfold PertExtension.Chart.fee; have hp:∀ z∈θU,0≤ R.scale*R.J z:=fun x hx=> (mul_pos h.scale (h.pos x hx)).le; have he:= hp x ht; have hl:=hp (-x) (by simpa [Metric.mem_ball] using ht); rw [max_eq_left he,max_eq_left hl,← ENNReal.toReal_ofReal he,← ENNReal.toReal_ofReal hl]; exact congr_arg ENNReal.toReal (even_fee h ht)
end Align
end
end YM.Contacts.Lyre
