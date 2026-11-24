import YM.LocalLTE.FieldPT.Curvature
/-!
 Kernel mode receipts continuing into actual Price.P: epoch and orientation before billing.
 Let the rotor $s.e$ represent proposals at all 0<s≤1 NOT continuation of physical theory.
 Delta response in `Kinetic.Charges` estimates for re-rendering.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {j k z l' M:ℕ} {W κ K U C V t H: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration
-- NB forcing exact Pole eventually K companion in all precision statement
structure DNA (X:RegularAddress n)(A:Option (Σ z,Art X z))(p:BudgetPoint)(z m K:ℕ)(κ:ℝ)(C:ℝ)(f:ℝ→ Pot G n) : Prop where
    sure:0≤C
    blank:A=Option.none→∀ i∈Weft.clip,f i=0
    arts (u:ℕ)(a:Art X u)(h:A=Option.some ⟨u,a⟩): u ≤ z ∧ Scene a.grove κ a.radius K m f C ∧ ∀ s∈Weft.clip,p.Regular X.support (f s)
namespace DNA
variable {A:RegularAddress n} {X:Option (Σ z,Art A z)}{p:BudgetPoint}{f:ℝ→ Pot G n}
lemma larger {k k' : ℕ} (h:DNA A X p z j k κ C f)(he:C≤ U)(ht:j≤ M)(hk:k≤k') (hp:z≤l'): DNA A X p l' M k' κ U f:=by
   refine ⟨h.sure.trans he,h.blank,fun i a hB=>?_⟩; obtain ⟨hy,hF,hG⟩:=h.arts _ a hB; exact ⟨hy.trans hp,(hF.generous _ hk he).padding ht,hG⟩ -- edit
lemma addMinus {g:ℝ→ Pot G n} (h:DNA A X p z j M κ C f) (H:DNA A X p z j M κ V g): DNA A X p z j M κ (C+V) (fun i=> f i-g i):=by
   refine ⟨add_nonneg h.sure H.sure,fun he s hs=>?_ , fun w a ha=> ?_⟩
   · rw [h.blank he _ hs,H.blank he _ hs,sub_self]
   obtain ⟨hz,hF,hJ⟩:=h.arts _ a ha; obtain ⟨_,hg,hV⟩:=H.arts _ a ha; exact ⟨hz,hF.lyric hg,fun i hi=> reg_sub (hJ _ hi) (hV _ hi)⟩
lemma nucleus {p : BudgetPoint}(h:DNA A X p z j M κ C f)(s:ℝ)(hs:s∈Weft.clip): p.Regular A.support (f s):=by
   rcases he:X with _|⟨u,a⟩; · rw [h.blank he _ hs]; exact reg_const _
   exact h.arts u a he|>.2.2 _ hs
-- predict from root.
def centered (m:ℕ)(H:ℝ)(K:ℕ):= Weft.Scene.scoreBp m K H
lemma rooted (h:DNA A X p z j M κ C f)(Θ:ℕ) (hp:Reliable G κ K) (hh:1≤ H )(H':∀ (o:Site n) (X:Grove o)(i:ℕ), i< z → Brush Θ H 1 ((X.crook i Chi.canonical κ (G:=G))∘Grove.soloV) 0) : Arp M Θ (C*centered j H Θ) (fun s=>f s∘ increment 1):=by
   rw [Hall.bare]; have hs: 0 ≤ centered j H Θ:= by unfold centered Weft.Scene.scoreBp; positivity
   rcases he:X with _|⟨u,a⟩
   · refine (Arp.zero'.climb le_rfl (mul_nonneg h.sure hs)).adjust (fun i hI=> ?_); rw [h.blank he _ hI]; rfl
   obtain ⟨hy,hF,hG⟩:=h.arts _ a he; exact Scene.glory _ hp hF Hall.zeroSolo p (H' _ _ _ (a.bonus.trans_le hy)) hh
lemma counted (hG:G.Simple) (h:DNA A X p z j M κ C f) (i l:PlaqAxes) (hp:Reliable G κ K)(hh:1 ≤ H)(H':∀ (o:Site n) (X:Grove o)(i:ℕ), i< z→ Brush 2 H 1 ((X.crook i Chi.canonical κ (G:=G))∘ Grove.soloV) 0) : Hex M (fun s=> projection A (f s) i l)∧ ∀ s∈Weft.clip,|s^2*projection A (f s) i l|≤ C* (centered j H 2 * (z:ℝ)^2) :=by
    rw [← mul_assoc]; let g s:=projection A (f s) i l
    rcases he:X with _|⟨u,a⟩
    · have ht s (hs:s∈Weft.clip): g s=0:=by
          unfold g; rw [h.blank he s hs]; unfold projection; split; next=> change logHessian (0:Config G n→ℝ) _ _=0; exact hessian_zero _ _ _
          rfl
      have hp':0≤centered j H 2:=by unfold centered Weft.Scene.scoreBp; positivity
      exact ⟨Hex.change Hex.blank (fun s hs=> (ht s hs).symm),fun s hs=>by rw [show projection A (f s) i l=0 from ht _ hs,mul_zero,abs_zero]; exact mul_nonneg (mul_nonneg h.sure hp') (by positivity)⟩
    have hC:= h.rooted 2 hp hh H'; obtain ⟨hy,hF,hK⟩:=h.arts u a he; apply Scene.implies hG A i l hC _ hK; rw [a.crisp]; exact Corona.halo_mono hy (Finset.Subset.refl _)
end DNA
-- bundle projection ledger.Sum
structure Genome (X:Listing G n)(V: Tour X z)(p:BudgetPoint)(i k:ℕ)(κ:ℝ)(f:ℝ→ℕ→Pot G n)(C:ℝ) : Prop where
    bills : ∃ c:ℕ→ℝ, anchored p X.reg c C ∧ ∀ i':ℕ,DNA (X.reg i') ((V i').map (fun k=>⟨z,k⟩)) p z (pie i+1) k κ (c i') (fun s=>f s i')
lemma Genome.raising {X:Listing G n}{V:Tour X z}{p:BudgetPoint}{f:ℝ→ℕ→Pot G n}(h:Genome X V p j k κ f C)(he:k ≤ M) (hV:C≤H):Genome X V p j M κ f H:=by
   obtain ⟨c,hc,hF⟩:= h.bills; exact ⟨c,fun i=>budget_loosen (hc i) hV,fun i=> DNA.larger (hF i) le_rfl le_rfl he le_rfl⟩
end YM.AnalyticBridge.VerifiedReset.Collection.Price
