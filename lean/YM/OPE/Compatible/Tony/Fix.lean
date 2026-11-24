import YM.OPE.Compatible.Tony.Noro
/-!
# Inner chamber translations and the exterior coordinate map

For valid boards and radii `r < b`, `Tride` shows that `Λace` commutes with the
inner chamber shifts `sailT`. `target` then transports directional derivatives
in the inner edge directions near zero for a smooth observable. Given a board
through radius `b + 1`, `railK` shows that the `bark b` data determine `Λace`.
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
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
variable (hp:Board n (r+1))(h:Board n b) (ht:r<b)
include hp in lemma ledgeT {x:Edge (Site n)}(hx:x∈fringe r n): Trim (r+1) x:=by
       rcases (regionH _ hp).mp (Or.inr hx) with ha|ha
       · have he:= (berthH _|>.mp ha); exact ⟨he.trans (Nat.le_succ _),(boulder x.2 x.1).2.trans (Nat.add_le_add_right he 1)⟩
       have he:= (berthH _|>.mp ha); let p:= (boulder x.2 (dotUp x)).1; rw [show dotUp x-step x.2=x.1 from add_sub_cancel_right ..] at p; exact ⟨p.trans (Nat.add_le_add_right he 1),he.trans (Nat.le_succ _)⟩
include hp ht
lemma noStory {x:Edge (Site n)}(hv:pdist x.1=b)(hz:pdist (dotUp x)=b): x∉fringe r n:=by intro h; rcases (regionH _ hp).mp (Or.inr h) with hx|hx<;> rw [berthH] at hx<;>omega
set_option maxHeartbeats 200000
omit ht h in
private lemma offField (x:D!) (u:Chamber G r) (e:Edge (Site n)) (he:e∉fringe r n) :
    represent (x+sailT G hp u) e=represent x e := by
  rw [arkL,arkL]
  apply congrArg G.lieExp
  change x (arkE e)+sailT G hp u (arkE e)=_
  rw [silly G hp u e he,add_zero]

include h in
private lemma agreeBorder (x:D!) (u:Chamber G r) :
    Agrees (↑(RingP b)) (expandAt 0 (represent (x+sailT G hp u))) (expandAt 0 (represent x)) := by
  intro i hi hV
  have hx : Moor i n∉fringe r n := noStory hp ht (StepsL.rise _ hi h) (by rw [←pier]; exact StepsL.rise _ hV h)
  unfold expandAt
  simp only [add_zero]
  exact offField hp x u (Moor i n) hx

include h in
private lemma stem_agrees (x:D!) (u:Chamber G r) (y:Site n) :
    stemL h (represent (x+sailT G hp u)) y=stemL h (represent x) y := by
  unfold stemL
  split
  · exact (quay b).trough _ _ _ (agreeBorder hp h ht x u)
  · rfl

include h in
private lemma row_outer (x:D!) (u:Chamber G r) (e:Edge (Site n)) (outside:¬Trim b e) :
    hermM h (represent (x+sailT G hp u)) e=hermM h (represent x) e := by
  unfold hermM
  rw [if_neg outside, if_neg outside,stem_agrees hp h ht,stem_agrees hp h ht]

include h in
private lemma edge_fixed (x:D!) (u:Chamber G r) (e:Edge (Site n)) :
    Λace G h (x+sailT G hp u) (arkE e)=(Λace G h x + sailT G hp u) (arkE e) := by
  rw [Pi.add_apply, vane_i, vane_i]
  split_ifs with inside
  · rfl
  · have hi:e∉fringe r n:=by
      intro hit
      obtain ⟨hx,hm⟩:=ledgeT hp hit
      exact inside ⟨hx.trans ht,hm.trans ht⟩
    rw [silly _ _ _ _ hi, add_zero, row_outer hp h ht x u e inside]

lemma Tride (x:D!)(u:Chamber G r): Λace G h (x+sailT G hp u)= Λace G h x+sailT G hp u:=by
  funext i
  obtain ⟨e,rfl⟩:=arkSur i
  exact edge_fixed hp h ht x u e
omit hp ht in
private lemma conserved_tangent {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L:E→E) (i v:E) (reg:DifferentiableAt ℝ L i)
    (shift:∀t:ℝ,L (i+t • v)=L i+t • v) : fderiv ℝ L i v=v := by
  have h₁ : HasDerivAt (fun t:ℝ=>L (i+t • v)) (fderiv ℝ L i v) 0 := by
    simpa only [zero_smul,add_zero] using!
      (HasFDerivAt.comp_hasDerivAt (f:=fun t:ℝ=>i+t • v) (l:=L) 0
        (by simpa only [zero_smul,add_zero] using reg.hasFDerivAt) ((YM.Stationary.ray_id v).const_add i))
  rw [show (fun t:ℝ=>L (i+t • v))=(fun t:ℝ=>L i+t • v) from funext shift] at h₁
  exact h₁.unique ((YM.Stationary.ray_id v).const_add (L i))

include h in
private lemma tangent_sail (i:D!) (z:Chamber G r) (diff:DifferentiableAt ℝ (Λace G h) i) :
    fderiv ℝ (Λace G h) i (sailT G hp z)=sailT G hp z := by
  apply conserved_tangent _ _ _ diff
  intro t
  rw [←map_smul]
  exact Tride hp h ht i (t • z)

omit hp ht in
private lemma bat_chain {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L:E→E) (g:E→ℝ) (u i:E) (dg:DifferentiableAt ℝ g (L i))
    (dL:DifferentiableAt ℝ L i) (fix:fderiv ℝ L i u=u) :
    bat u (g ∘ L) i=bat u g (L i) := by
  unfold bat
  rw [fderiv_comp i dg dL,ContinuousLinearMap.comp_apply,fix]

omit hp ht in
private lemma bat_near {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L:E→E) (g:E→ℝ) (v:E) (dg:ContDiffAt ℝ ω g 0) (dL:ContDiffAt ℝ ω L 0) (zero:L 0=0)
    (fix:∀i,DifferentiableAt ℝ L i → fderiv ℝ L i v=v) :
    bat v (g ∘ L)=ᶠ[𝓝 0] (bat v g) ∘ L := by
  have lim:Tendsto L (𝓝 0) (𝓝 0) := by simpa only [zero] using dL.continuousAt.tendsto
  filter_upwards [lim.eventually (dg.eventually (by simp)),dL.eventually (by simp)] with i hi he
  exact bat_chain L g v i (hi.differentiableAt (by simp)) (he.differentiableAt (by simp))
    (fix i (he.differentiableAt (by simp)))

include h in
private lemma fixed_edge (e:↥(fieldP r)) (x:G.ColorIndex) (i:D!) (diff:DifferentiableAt ℝ (Λace G h) i) :
    fderiv ℝ (Λace G h) i (functorE (0:Site n) e.val x)=functorE 0 e.val x := by
  rw [←ferryT G hp e x]
  exact tangent_sail hp h ht i (PickL G (e,x)) diff

lemma target (e:↥(fieldP r))(x:G.ColorIndex)(g:D!→ℝ)(hk:ContDiffAt ℝ ω g 0):
    bat (functorE (0:Site n) e.val x) (g ∘ Λace G h)=ᶠ[𝓝 0] (bat (functorE 0 e.val x) g) ∘ Λace G h:=by
  exact bat_near (Λace G h) g (functorE (0:Site n) e.val x) hk (haloStage h G) (eΛ h G)
    (fixed_edge hp h ht e x)
omit hp ht
lemma railK (hx:Board n (b+1))(x y:D!)(he: BlurD G (bark b) n x=BlurD G (bark b) n y): Λace G h x=Λace G h y:=by
       have ht(e:Edge (Site n))(h:Trim b e):x (arkE e)=y (arkE e):=by
            obtain ⟨z,hz,h⟩:=edgeMy e hx h; have hm:= congr_fun he (⟨z,hz⟩:↥(bark b)); rw [←h];rw[echoP,echoP] at hm; exact hm
       have hp:hermM h (represent x)=hermM h (represent y):= beamOut h _ _ hx (fun i hE hF=>by rw [arkL,arkL,ht i ⟨hE,hF⟩]); funext i; obtain ⟨i,h⟩:=arkSur i; rw[←h,vane_i,vane_i,hp]; split; rw[ht i (by assumption)]; rfl
end YM.OPE.Merchant
