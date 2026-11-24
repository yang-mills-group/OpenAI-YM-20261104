import YM.Qlocal.Reckoner.Cardinals
import YM.Qlocal.Caption
/-!
 The Caption λ.exterior, not approximated when choosing Epoch: EXACT on any multi-marker including mixed coarse and remains charged on footprint. Use as analytic row directly in Epoch preparation, or as error e_t to recover smaller currency.Can also bind at ingress to use next step numbers; for the Ψ log calculation *model* Caption rank0 if generated there see `Gauge.Labor`: treated as masked part of formal root receipt, not stranded here yet.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Gauges.Caption
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Reckoner
open AnalyticBridge VerifiedReset Collection -- adjust
open Parabola Scribe
variable {Ω ι J J' J₀ V K κ : Type} {G:Gauge}{c f:Side}
    {P: RG.Rep G f}{P': RG.Rep G c} [DecidableEq V]{R:Marker.Census V}
    {o:V→Site f}{s:V→Support f}{q:R.Mode→ℝ}{p:BudgetPoint}
    {A A' δ τ w r e v:ℝ} (S:StepData c f)
variable (Y:Taste Ω o P R){dcl:Set (ℕ ×ℕ)}
    (hp:RetainsDeclared dcl Y s) (h₀:Peak P o Y q P.p.supportExponent A A') (p':Rental q)
local notation "u★"=> StageArt.fly S.ratio ∘ s
noncomputable def body : Scribe Ω ℕ G c R:= ⟨Y.tag, StageArt.fly S.ratio ∘ Y.site,fun _=>True,fun x i _=> Y.score x i⟩
local notation "U★" => body S Y
-- complex.ofReal(1)*ℂ.Const.
lemma forever (X:Support c)(p:BudgetPoint)(v:ℂ)(x:Site c) : p.Regular X (fun _ :Config G c=>v)∧p.supBounds x X (fun _ : Config G c=>v) ‖v‖:=by
 let F: Config G c→ℝ:=fun _=>1; let g:= Complex.ofReal ∘ F; have hQ:p.Regular X F:= CouplingShape.reg_const _; have ht:=Blush.pricingG hQ (show p.supBounds x X F |1| from CouplingShape.sup_const _); rw [show (fun _: Config G c=>v)=v • g from (by funext i; exact (mul_one v).symm), ← mul_one ‖v‖, ← (show |(1:ℝ)|=1 from abs_one)]; -- last rw repeats v? actual subtype.
 exact ⟨Next.Foundations.regular_smul v (ornate hQ), Next.Foundations.bound_smul v ht⟩
include hp h₀
lemma carried [Nonempty Ω] : Proper (body S Y) P'.p u★:=by
 let x:Ω:=Classical.ofNonempty; have he(i): (Y.tag i).val.Nonempty:= (h₀.active x).captions.card i
 refine ⟨?_,fun x i=> ?_,fun i v x U h hh=> ?_,?_,fun _ _ _ _=>rfl⟩
 · intro i; obtain ⟨j,hj⟩:=he i; exact ⟨S.ratio.parent (o j), mem_image_of_mem _ (hp.captions i j hj (hp.origins j))⟩
 · exact (forever (U★|>.region i) P'.p (Y.score x i) (0:Site c)).1
 · exact Finset.image_subset_image (hp.captions i v hh)
 intro i h; exact ((he i).ne_empty (congr_arg Subtype.val h)).elim
variable (hB:P.p.B≤ 2*P'.p.B)(hk:P'.p.supportExponent*Footprint.conversion S.ratio 0≤ P.p.supportExponent)
omit hp
include h₀ p' hB hk in
lemma lasting : Spend (body S Y) P'.p q P'.p.supportExponent (StageArt.cost S P'.p.supportExponent*A):= by
 obtain ⟨g,hg,hG,hT⟩:=h₀.captions; refine ⟨g,⟨hg,fun i k u hu=> Local.bound_weaken (forever _ _ _ _).2 (hG i k)⟩, StageArt.transfer (fun i=>mul_nonneg (p'.pos _|>.le) (hg i)) hT hB P'.p.B_pos P'.p.exponent_pos.le hk⟩ -- annotation measure size
omit h₀ in
lemma words (p:BudgetPoint)(x:Ω)(U:Config G c) : (body S Y).send p x U=(Y.leaf x).captions.chord:= tsum_congr fun i=> by change Poly.send _ (render (body S Y) _ _ _ _)= _; rw [render,if_pos (show (U★).total i from trivial)]; rfl
variable [Fintype V]
variable (g:Ω→ Config G c→ Poly R) (o': V→ Site c)
    (X:Scribe Ω J G c R) (E:Scribe Ω J' G c R)(T:Scribe Ω J₀ G c R) (K:Source G c Ω R)
    (h: Certified P' (StageArt.fly S.ratio ∘ s) q P'.p.supportExponent v τ r e X E T K g)
local notation "Φ"=> E.pile T
local notation "Ps"=> P'.p
include h hp h₀ p' hk hB
lemma hears [Nonempty Ω] : Certified P' u★ q P'.p.supportExponent v τ r (e+StageArt.cost S P'.p.supportExponent*A) X E (T.pile (body S Y)) K (fun i y=>Poly.pass ((Y.leaf i).captions.chord) * g i y):=by
 obtain ⟨x,hX,y,hE,t,hT,hK,h⟩:= h; let T':= (body S Y); let u :=x.pile (y.pile t); let U₀ := Spend.pile hX (Spend.pile hE hT); have hz:= carried (P':=P') S Y hp h₀; have he:= lasting S Y h₀ p' hB hk
 refine ⟨x,hX,y,hE,t.pile hz,Spend.pile hT he,hK,?_⟩
 rw [← h]; let v:= (u★); have ht:= P'.p.exponent_pos.le; rw [reorder (T:=T'.pile (X.pile Φ)) ?_]; funext i b; rw [pile_density p' hz u he U₀ ht,words]
 funext i b; rw [pool x (y.pile (t.pile hz)) hX (Spend.pile hE (Spend.pile hT he)) p' ht,pool y (t.pile hz) hE (Spend.pile hT he) p' ht, pool t hz hT he p' ht,pool hz u he U₀ p' ht,pool x (y.pile t) hX (Spend.pile hE hT) p' ht, pool y t hE hT p' ht]; abel
end YM.Qlocal.Gauges.Caption
