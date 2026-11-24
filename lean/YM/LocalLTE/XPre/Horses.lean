import YM.LocalLTE.XPre.Society
import YM.LocalLTE.Dilation.Silhouette
/-!
# Keep lookup-scripts of the singleton door when splitting the candidate
into forecast hats and unadmitted hats. `Odyssey` needs exact coherence
at the actual door. Uses *exact*, even at bad fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι: Type}{G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ K ν t u q r s b:ℝ} {A:Activities G f} {d p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations
variable {v w:ℂ}{X:Wing→Prop}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
variable {E:Config G f→ℂ} {Z: Res G f}{W : Res G c}
-- Cloud z complex φ. Push contributions.
variable (T:Blush.Cloud R)
-- include all supports.Wing T typology.
noncomputable def readLeaf (i:Bool):= if i then T.live else T.pale
noncomputable def lit (i:Bool):ℂ:= if i then 1 else Complex.I
-- spelling addresses.
local notation "b'"=> ∑ i:Bool,lit i • prose (readLeaf T i)
local notation "x'"=> ∑ i:Bool,lit i • entry (readLeaf T i)
local notation "d'"=> ∑ i:Bool,(v*lit i) • quoted L (readLeaf T i)
local notation "F'" => 2 *load T.live
set_option quotPrecheck false
-- actual grants vary, need unprize with linear.G.
lemma challenge {ψ: MergeProof.Response G c} (h:X T.live.turn) (ho:o∈T.live.crest)
    (hp:E=∑ i:Bool, lit i • prose (readLeaf T i)) (hx:Z=x') (hg: W=d'+hook C.activities C.p.threshold ψ)(hv:Attainment C.p o' ψ s):
    Odyssey X o o' v E Z W 0 (2*load T.live) s L (readLeaf T) lit ψ :=by
    let A i:= load (readLeaf T i); have he(i):X (readLeaf T i).turn:=by cases i; exact T.together ▸ h; exact h
    have h'(i:Bool):o∈ (readLeaf T i).crest:=by cases i; exact T.turnout ▸ ho;exact ho
    have hc(i:Bool):A i=load T.live:=by cases i; unfold A load;rw [show (readLeaf T false).crest=T.live.crest from T.turnout.symm, show (readLeaf T false).weight=T.live.weight from T.rates.symm]; rfl -- order? 
    refine ⟨fun i=>⟨h' i,he i⟩,⟨fun i=> mul_nonneg (norm_nonneg _) ((Leaf.profit _).trans (R.p.loMass _ _ (Leaf.profit _))),Summable.of_finite,?_⟩,hv,fun U=>?_,fun j U=>?_,fun i U=>?_⟩
    · rw [tsum_fintype]; change ∑ i,‖_‖ *A i≤_; rw [Fintype.sum_bool,hc,hc,show ‖lit true‖=1 from norm_one, show ‖lit false‖=1 from Complex.norm_I]; rw [one_mul,two_mul]
    · rw [sub_zero,hp,Finset.sum_apply]; exact hasSum_fintype _
    · rw [hx,Finset.sum_apply, Finset.sum_apply]; exact hasSum_fintype _
    rw [hg]; simp only [Pi.add_apply,add_sub_cancel_right, Finset.sum_apply]; exact hasSum_fintype _
end YM.LocalLTE.XPre
