import YM.OPE.Compatible.Song.Div
import YM.OPE.Compatible.Song.Grip
import YM.OPE.Compatible.Song.Tan
/-!
# Warp α bill at armed request
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL
variable {i j d k m r l b:ℕ}{n:Side}
variable {I W:Type} {B:I→ Finset (Edge Cover)}{N:I→ Side}{φ:Filter I}{Z:I→ℝ}
variable {M:I→ℕ}(A:Audience φ Z N M r)(f g:GlyphQ G N)(T:I→ Law (Chamber G r))
namespace Shroud
variable (u:GlyphQ G N)(k:ℕ)(V:∀ i, Board (N i) (r+1)) (S:Shroud A f g T) (h:Filμ (fun i=>bark (M i)) φ Z u d) (he:∀ᶠ i in φ, LevelA (tor (N i)) (u i))
set_option maxHeartbeats 200000
include h S
set_option maxHeartbeats 200000 in
open Lean Meta Elab Tactic in
elab "match_account_types " h:ident : tactic => withMainContext do
  let simplifyTypes (e:Expr) : MetaM Expr := do
    let names:= #[``Bid.Dir,``Exterior.fieldDir,``Libra.Keys,``Chamber]
    transform e (pre:=fun x=>do
      let reduced:=x.headBeta
      if reduced != x then return .visit reduced
      if let .const name _:=x.getAppFn then
        if names.contains name then
          if let some expanded ← unfoldDefinition? x then return .visit expanded
      return .continue)
  let id ← getMainGoal
  let witness ← getFVarId h
  let posed ← simplifyTypes (←id.getType)
  let paid ← simplifyTypes (←witness.getType)
  unless ← withReducible (isDefEq posed paid) do
    throwError "the normalized Gaussian invoices differ"
  id.assign (mkFVar witness)
  replaceMainGoal []

omit h S in private lemma spinV {L:I→Law (Chamber G r)} (K:(i:I)→ Bid.Dir G (N i)→ₗ[ℝ] Dual' (Bid.Dir G (N i)))(hp:∃ c:ℝ,0 < c ∧∀ᶠ i in φ,∀ x: Chamber G r,c*‖x‖^2 ≤ (L i).P x x)(hT:Tendsto Z φ atTop)(ht:Bills φ Z u)(hv:∀ᶠ i in φ,Tall (u i) d)(h:Bills φ Z (fun i x=> mate (sailT G (V i)) (K i) (L i) x)): Bills φ Z (fun i=>OrientX.νrt (K i) (sailT G (V i)) (L i) (u i) k):=by
  refine Marks (G:=G) (D:=fun i=>Body 1 (N i)) (F:=↥(fieldP r))
    (fun i=>sailT G (V i)) K L k u hT hp ?_ ?_ ht hv
  · obtain ⟨b,hb,H⟩:=h
    refine ⟨b,hb,H.mono ?_⟩
    intro i bill x small
    have paid:=bill x small
    match_account_types paid
  · intro i x
    have old:=sailX G (V i) x
    match_account_types old

lemma fundV : Bills φ Z (fun i=>scion f T u k i V) :=by
  unfold scion
  apply spinV u k V (fun i=>chrom (f i)) S.rise A.fair h.loud h.tariff
  obtain ⟨b,hb,H⟩:=S.polesξ A f g T V
  refine ⟨b,hb,H.mono ?_⟩
  intro i bill x small
  exact bill x small
omit h S in
private lemma funds {D:I→Type} [∀ i,NormedAddCommGroup (D i)][∀ i,NormedSpace ℝ (D i)] {W:Type}[Fintype W] (P:(i:I)→D i→ Libra.Keys G W)(h:Bills φ Z P) (w:W): Bills φ Z (fun i (x:D i)=> P i x w):=by
        obtain ⟨b,hb,H⟩:=h; exact ⟨b,hb,H.mono (fun i hi x hx=> (norm_le_pi_norm (P i x) w).trans (hi _ hx))⟩
include he
lemma shard (e:↥(fieldP r)):
       let g:= fun i (x:Bid.Dir G (N i))=> scion f T u k i V x e; Bills φ Z g ∧∀ᶠ i in φ,FirmR (bark (M i)) (g i) k:=by
       intro p; have hp := eman A f g T u k V S h he; refine ⟨funds _ (fundV A f g T u k V S h) e, hp.mono fun i hi=>?_⟩; obtain ⟨hx,hr,hq,hT,ht⟩:=hi; refine ⟨?_ , ⟨fun x y h=>congr_fun (hx.jury _ _ h) e⟩,(fun x y=>congr_fun (hT _ _) e),fun g x=> congr_fun (ht x g) e⟩; apply Eq.symm (Tall.pint (f:=p i) ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:↥(fieldP r)=> G.Color) e).contDiff.comp hq) ?_); intro x t; let y:=scion f T u k i V; have hy:y (t • x)=t^k • y x:=(congr_fun hr _).trans ((homogeneous ..).trans (congr_arg _ (congr_fun hr x).symm)); exact congr_fun hy e
end Shroud
end YM.OPE.Merchant
