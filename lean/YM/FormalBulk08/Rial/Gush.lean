import YM.FormalBulk08.Rial.Pond

/-! Coherent slice readouts. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rial
open Filter Set Function Lattice Laurent Wilson Exterior Stationary
open Orb Reef Jets Lava Lotus Mesa Gorge Shore City Kemp Rift Wine Pose PowerSeries Wick
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {S:Finset Cover} {d:ℕ} {F: Frame G d} {I E:Type*} {j u l r D:ℕ} {η A : ℝ}
variable (T:SectionData F) (H:Hol G)(h:T.Sound H)(hx:Bid.pop T)(a:Loc G 1) (i:Letter F)
include a in
lemma terraced (j:ℕ)(p:Fin l → Snap G d): Tensor.coeff (Tensor.diagonal (Tensor.coeff (lights T (mint F i)) j 0) ∘ (funnels T.stencil)) l 0 p=
   slate (hymn (rancho (paste (lights T (mint F i))) j j)) d l p:= by
   let V:=SpotC T.stencil G; let κ:=rancho (paste (lights T (mint F i))) j j
   have he : (Tensor.diagonal (Tensor.coeff (lights T (mint F i)) j 0) ∘ (funnels T.stencil))=
     ∑ t:chain V j, κ t • tier (d:=d) (chamber _ _ ∘ t):= by ext x; rw [Finset.sum_apply]; exact grounds T (mint F i) j x
   rw [he];exact (Pose.stack_val Finset.univ κ _ p (fun t _=> (tier_diff (chamber T.stencil G ∘ t)).of_le le_top)).trans (anthem_slate a κ d l p).symm
lemma tablets {E D: Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D](p:E→ℝ) (u:D→E)
    (m:ℕ)(h: ContDiffAt ℝ m p 0)(he: ContDiffAt ℝ m u 0)(hv: u 0=0) : Tensor.coeff (p ∘ u) m 0=∑ i∈Finset.range (m+1),Tensor.coeff (Tensor.diagonal (Tensor.coeff p i 0) ∘ u) m 0:= by
   let P:=Work.G05.blockTaylor m p; have H' : ContDiff ℝ m P:= Work.G05.blockTaylor_contDiff ..
   have H : Tensor.coeff (p∘u) m 0=Tensor.coeff (P∘u) m 0:=congr_arg _ (Work.G05.jets_comp (g:=p) he he (hv.symm ▸ h) H'.contDiffAt rfl (fun _ _=>rfl) (fun a ha=> by rw [hv]; exact (Work.G05.blockTaylor_jets h a ha).symm) m le_rfl)
   rw [H, show P ∘ u= ∑ i∈Finset.range (m+1),Tensor.diagonal (Tensor.coeff p i 0) ∘ u from funext fun x=> by simp only [Finset.sum_apply,Function.comp_apply,P,Work.G05.blockTaylor] ]
   exact Tensor.coeff_sum _ _ _ _ (fun i _=> (Tensor.diag_smooth _ _).contDiffAt.comp _ he)
set_option maxHeartbeats 600000 in
lemma banking (a:Loc G 1) (j:ℕ) : Tensor.coeff (hive T i) j 0=∑ u∈Finset.range (j+1), slate (hymn (rancho (paste (lights T (mint F i))) u u)) d j := by
    unfold hive;rw [tablets (lights T (mint F i)) _ _ ((lights_diff ..).contDiffAt.of_le le_top) (funnels_diff.of_le le_top) funnels_zero]
    refine Finset.sum_congr rfl fun u _=>?_ ; ext p; exact terraced T a i u p
-- complex lift
variable {E J : Type*}
lemma ascend {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (f:E→ℝ)(h:ContDiffAt ℝ l f 0)(x : Fin l→ E): Tensor.coeff (Complex.ofRealCLM ∘ f) l 0 x = ((Tensor.coeff f l 0 x:ℝ):ℂ):= by
   unfold Tensor.coeff;rw [Complex.ofRealCLM.iteratedFDeriv_comp_left h le_rfl]; simp only [_root_.smul_apply,smul_eq_mul]; rw [Complex.ofReal_mul, Complex.real_smul]; rfl
include h H
set_option maxHeartbeats 600000 in
lemma diagonal_lifts (x:Slate G d l)(m:ℕ)(hp:l≤ d)(hk:m≤d)(hb:x=Tensor.coeff (hive T i) l 0) :
   lent x m=gradePart (m,l) (F.basis (mint F i)):= by
    let P:= slant T (copy F (mint F i))∘ Film.localLane (d:=d); have Hs:=Film.still T h (copy F (mint F i)); let Q:= Parts.archive Hs
    have hu: ContDiffAt ℝ l (hive T i) 0:=  (show ContDiffAt ℝ l (lights T (mint F i)) (funnels T.stencil (0:Snap G d)) from ((lights_diff T _).of_le le_top).contDiffAt).comp _ ((funnels_diff (S:=T.stencil) (G:=G) (d:=d)).of_le le_top)
    have he : Tensor.coeff P l 0=tide x:= by
       ext y; unfold P; rw [←lysine T H h i,tide_at,hb,ascend _ hu]
    have hm : Q= F.basis (mint F i):= Eq.trans (corner T h _) ((F.coords.injective (by simp [copy])))
    have hg:=Parts.capture Hs hk hp; change (gradePart _ Q).val= WardBin.tile (Tensor.coeff P l 0) _ at hg
    rw [hm,he] at hg; rw [lent,← hg];exact pieceL_apply ..
end YM.FormalBulk08.Rial
