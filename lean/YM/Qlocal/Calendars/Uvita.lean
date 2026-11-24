import YM.Qlocal.Gauges.Voice
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
local notation "u★" => StageArt.fly S.ratio ∘ s
local notation "U★"=> body S Y
variable {e0:ℝ} (h0:0≤e0) (hB:P.p.B≤ 2*P'.p.B)(hk:e0*Footprint.conversion S.ratio 0≤ P.p.supportExponent)
include h0
include h₀ p' hB hk in
lemma lastingB : Spend (body S Y) P'.p q e0 (StageArt.cost S e0*A):= by
 obtain ⟨g,hg,hG,hT⟩:=h₀.captions; refine ⟨g,⟨hg,fun i k u hu=> Local.bound_weaken (forever _ _ _ _).2 (hG i k)⟩, StageArt.transfer (fun i=>mul_nonneg (p'.pos _|>.le) (hg i)) hT hB P'.p.B_pos h0 hk⟩ -- annotation measure size
variable [Fintype V]
variable (g:Ω→ Config G c→ Poly R) (o': V→ Site c)
    (X:Scribe Ω J G c R) (E:Scribe Ω J' G c R)(T:Scribe Ω J₀ G c R) (K:Source G c Ω R)
    (h: Certified P' (StageArt.fly S.ratio ∘ s) q e0 v τ r e X E T K g)
local notation "Φ"=> E.pile T
local notation "Ps"=> P'.p
include h hp h₀ p' hk hB
lemma tells [Nonempty Ω] : Certified P' u★ q e0 v τ r (e+StageArt.cost S e0*A) X E (T.pile (body S Y)) K (fun i y=>Poly.pass ((Y.leaf i).captions.chord) * g i y):=by
 obtain ⟨x,hX,y,hE,t,hT,hK,h⟩:= h; let T':= (body S Y); let u :=x.pile (y.pile t); let U₀ := Spend.pile hX (Spend.pile hE hT); have hz:= carried (P':=P') S Y hp h₀; have he:= lastingB S Y h₀ p' h0 hB hk
 refine ⟨x,hX,y,hE,t.pile hz,Spend.pile hT he,hK,?_⟩
 rw [← h]; let v:= (u★); have ht:= h0; rw [reorder (T:=T'.pile (X.pile Φ)) ?_]; funext i b; rw [pile_density p' hz u he U₀ ht,words]
 funext i b; rw [pool x (y.pile (t.pile hz)) hX (Spend.pile hE (Spend.pile hT he)) p' ht,pool y (t.pile hz) hE (Spend.pile hT he) p' ht, pool t hz hT he p' ht,pool hz u he U₀ p' ht,pool x (y.pile t) hX (Spend.pile hE hT) p' ht, pool y t hE hT p' ht]; abel
end YM.Qlocal.Gauges.Caption
