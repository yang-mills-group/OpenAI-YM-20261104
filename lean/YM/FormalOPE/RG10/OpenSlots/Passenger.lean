import YM.FormalOPE.RG10.OpenSlots.Pipeline
/-!
 # Multi-mark pin-stamp full (open chart) journey; compare to independent top rule
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof Router Quadratic
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {n: Side} {J:ChartRatio G}
variable {L: Fabric G n} (T:Cloth L) (z:L.Accounts→PowerSeries ℝ) (H:∀ i,0<term (z i) 0)(HJ:LocalRatio J)
 def purchase (A:Ticket (Flats G n)): PowerSeries ℝ:= course T (z∘some) (initialFull G n (z none)) J A (released HJ (paidRoot T J z H))
theorem stock (A:Ticket (Flats G n)) : purchase T z H HJ A= enjoy (evidence _ (enough L T.choose z H).entire) (tangent G T.choose.Bulk) (boost (castAt T) A) (Stack.weight J (model L T.choose z)):= by
 unfold purchase; rw [earns HJ A (paidRoot T J z H) (OpenSlots.restores _ firstBill), recorded _ _ _ _ (checked_up HJ)] -- type
variable {O : Wilson.Config G n→ ℝ}
-- log-link full basis imbed, curvature chart on OEdge. prove smooth given restrictedO only!
 def imprintRoot (O:Wilson.Config G n→ℝ): Ticket (Flats G n):= imbed (O ∘ Orb.liftLinks)
include T in
lemma covariant (h:Orb.PreTest O): ContDiffAt ℝ ∞ (O ∘ Orb.liftLinks ∘ expLinks G _) 0:= by
 let Φ(x:Flats G n): L.LinksOn:= L.combine (expLinks G _ x) 1; let F:= attending L O
 have H0u:Φ 0=1:= by funext i; cases i<;> first| exact congr_fun identity_zero _|rfl
 have HF x: O (Orb.liftLinks (expLinks G _ x)) = F (T.choose.treeGauge (Φ x)):= ((eligible L h).reading.leg _ (T.choose.frame_root _) (Φ x)).symm
 let q:= T.choose.bulk ∘ Φ
 let p:= F ∘ T.choose.board
 have he:(O ∘ Orb.liftLinks ∘ expLinks G _)= p ∘ q:= funext fun x=> by change O _= F (T.choose.board (T.choose.bulk (Φ x))); rw [comp_apply,HF x, Loom.Truss.board_bulk]
 rw [he]; have hq:q 0=1:= by simp [q,H0u]
 have hf : MatDiffAt q 0:= T.choose.bulk_diff (fun i=> by cases i with
                                                              | inl i=> exact neighborhood_exp i
                                                              | inr=> exact contDiffAt_const)
 have hp: ContDiffAt ℝ ω (Inherit.down ∘ q) 0:= down_chart hf hq; have hv:= ((eligible L h).passes _ T.choose).germ
 have hi: (p ∘ q)=ᶠ[𝓝 0] (p ∘ expLinks G T.choose.Bulk) ∘ (Inherit.down ∘ q):= by
    have hh:= hf.continuousAt.tendsto; rw [hq] at hh
    filter_upwards [hh.eventually down_right] with x hX using congr_arg p hX.symm
 exact (ContDiffAt.comp _ (by simpa only [comp_apply,hq,down_one] using hv : ContDiffAt ℝ ∞ (p ∘ expLinks G T.choose.Bulk) ((Inherit.down∘q) 0)) (hp.of_le le_top)).congr_of_eventuallyEq hi
lemma request (h:Orb.PreTest O): boost (castAt T) (imprintRoot O)= imbed (attending L O ∘ T.choose.board):= by
 unfold imprintRoot imbed; rw [Vault.climbing (castAt T) (show ContDiffAt ℝ ∞ ((O ∘ Orb.liftLinks) ∘ expLinks G _) 0 from covariant T h)]; congr 1; ext1 x; simp only [comp_apply, accord_top, attending]

theorem diagram (hw:z none=1) (h:Orb.PreTest O): purchase T z H HJ (imprintRoot O) = PowerSeries.mk (Orb.diag (Orb.restrictedO O)):= by unfold purchase; rw [earns HJ _ (paidRoot T J z H) (OpenSlots.restores _ firstBill), request T h]; exact top_projection T z HJ H hw h
-- products integrated at once, before optional Treasury marker logarithm
include T in
lemma rootOfProduct {α:Type}(s:Finset α)(a:α→Wilson.Config G n→ℝ)(h:∀ i∈s,Orb.PreTest (a i)): imprintRoot (∏ i∈s, a i)=∏ i∈s, imprintRoot (a i):=by
 have H'(i:α)(hi:i∈s): Curtain (a i ∘ Orb.liftLinks) := by
     refine ⟨((h i hi).continuous.comp (Orb.lift_cont G)).measurable,?_,covariant T (h i hi)⟩
     obtain ⟨m,hm⟩:= isCompact_univ.exists_bound_of_continuousOn ((h i hi).continuous.comp (Orb.lift_cont G)).continuousOn; exact ⟨m,fun u=> hm _ (Set.mem_univ _)⟩
 simp_rw [imprintRoot]; rw [show (∏ i∈s, a i) ∘ Orb.liftLinks=(∏ i∈s, (a i ∘ Orb.liftLinks)) from funext fun i=> by simp [Finset.prod_apply]]; exact label_prod _ _ H'
end YM.FormalOPE.RG10.OpenSlots
