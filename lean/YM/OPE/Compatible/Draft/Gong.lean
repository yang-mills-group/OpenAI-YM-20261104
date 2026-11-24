import YM.OPE.Compatible.Draft.Billet
/-!
# Stanley coherence. Defused current through product
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n c f:Side}
open Wilson RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp Pilot
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable {i j:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {S: StepData c f} {H: Even c.val}
local notation "μ"=> even_both S.ratio H
local notation "J!"=> Rill.rollB S H
variable {A:Alps B Q i l}{Y: Bor (even_both S.ratio H) A b} (U:Plot (even_both S.ratio H))(t:S.Choices)
protected abbrev fineWar (F:(Tableau S H).Stand ({origin μ}:Set _))(x:Keys G F.Free):= worldF S H t A (F.rollX x)
include U
lemma stems (Z: Bor (even_both S.ratio H) A b){u:Tile G U.Free→Tile G (Limb H)} (F:Hark u) (hf:u=ᶠ[𝓝 1] braveP S H U t)(h:S.patch.Branches S.kernel G):
   (worldF S H t A∘ (StemX S H U).rollX) ∘ F.crown (piBond S H U) =ᶠ[𝓝 0] roomP (piBond S H U) (Z.L U) (wellX S H b) ∧
   (worldW S H t b A∘ (StemX S H U).rollX) ∘ F.crown (piBond S H U) =ᶠ[𝓝 0] weightP (piBond S H U) (Z.L U) (wellX S H b):=by
       let T:= StemX S H U; let p:=piBond S H U; let L:= Pilot.prL p G; let R:= prR p G; let B:=F.crown p
       let P:= (U.rollX (G:=G)).toContinuousLinearMap.comp L
       have hp: Tendsto P (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! P.continuous.tendsto 0
       have ht:∀ᶠ i:Keys G T.Free in 𝓝 0,lo_left S H G (T.rollX (B i))=P i := by
            filter_upwards [F.outlookZ p] with i h; rw [show lo_left S H G (T.rollX (B i))= _ from beamAt S H U _, h.1]; rfl -- p defeq
       have he := pulseZ S H t U h F hf
       constructor
       · filter_upwards [hp.eventually Z.u,ht,he] with i hx hh he; change mural μ A _- _+ noiseC _ _ _ (T.rollX (B _)) = (Z.L U).f (L i)+_; rw [hh, show noiseC _ _ _ _= _ from he, ← hx, Z.acts];rfl
       filter_upwards [hp.eventually Z.t,ht,he] with i hx hh he; change tintT μ A b _* Real.exp (-b*noiseC _ _ _ (T.rollX (B _)))=(Z.L U).w (L i)*_;rw [hh, show noiseC _ _ _ _= _ from he, ← hx, Z.serves];rfl
omit U
lemma narrated (h:S.patch.Branches S.kernel G): ContDiffAt ℝ ω (noiseC S H t (G:=G)) 0:=by
       let U:= Keys G J!; let P:=lo_left S H G; let K:=lo_right S H G; let R:=fun x:U=> cloak (G:=G) μ (P x); let Q:=fun x:U=> (cloak H) (K x); let L : U→ Lattice.Links (Per f) G.El:= represent ∘ R; let V : U →Config G c:= represent ∘ Q
       have hp: YM.Stationary.Army L 0:= by intro i; simp only [L,Function.comp_apply, Work.F03.represent_link]; apply ContDiffAt.comp (f:=fun x:U=> R x _ ) _ (G.exp_jet.contDiffAt); exact ((contDiffAt_apply ..).comp _ ((cloak μ).contDiff.contDiffAt.comp _ P.contDiff.contDiffAt))
       have hv: YM.Stationary.Army V 0:= by intro i; simp only [V,Function.comp_apply,Work.F03.represent_link]; exact G.exp_jet.contDiffAt.comp (f:=fun x:U=> Q x _) _ ((contDiffAt_apply ..).comp _ ((cloak H).contDiff.contDiffAt.comp _ K.contDiff.contDiffAt))
       have hY:L 0=1:=by unfold L R; rw [Function.comp_apply,map_zero,map_zero,link_one]
       have hx := YM.Stationary.Army.pred (S:=S) h t hp hY
       unfold noiseC noiseTaylor; simp_rw [← cloak_e]; apply ContDiffAt.div_const; apply ContDiffAt.mul contDiffAt_const; refine ContDiffAt.sum fun i _=>?_ ; exact YM.Stationary.matrix_price_jet (A:=fun j:U=> V j i*(S.prediction (L j) t i)⁻¹) ((hv i).mul (hx.inv i)) -- need G.mat_mul
end YM.OPE.Cascade.Rill
