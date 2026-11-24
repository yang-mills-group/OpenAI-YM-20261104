import YM.OPE.Compatible.Draft.Fern
/-!
# Joint test = actual Fine iris. exact all characters in H (not physical states before matching).
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
variable {A:Alps B Q i l} (Z:Bor (even_both S.ratio H) A b) (t:S.Choices) (h:S.patch.Branches S.kernel G)
namespace Elm
variable (D:Elm A S H t b)
include h
lemma waltz: (Tableau S H).Walks D.f D.w:=by
     refine ⟨((safeF t h A).of_le le_top|>.congr_of_eventuallyEq D.ok),((safeW t h A).of_le le_top|>.congr_of_eventuallyEq D.up),fun {x y s} hp=>?_,fun {x y s} hp=>?_⟩
     · apply (isBigO_zero _ _).congr' _ Filter.EventuallyEq.rfl; have hX:Tendsto x Tested.germ (𝓝 0):= hp.gx ▸ hp.hX.continuousAt.continuousWithinAt; have hY:Tendsto y Tested.germ (𝓝 0):=hp.gy ▸ hp.hY.continuousAt.continuousWithinAt
       filter_upwards [hp.law.filter_mono nhdsWithin_le_nhds,hX.eventually D.ok,hY.eventually D.ok] with i hi ha hb; rw [ha,hb,show worldF _ _ _ A _= worldF S H t A (y i) from (loft (b:=b) t h _ _ _ hi).1]; ring
     apply (isBigO_zero _ _).congr' _ Filter.EventuallyEq.rfl; have hX:Tendsto x Tested.germ (𝓝 0):= hp.gx ▸ hp.hX.continuousAt.continuousWithinAt; have hY:Tendsto y Tested.germ (𝓝 0):=hp.gy ▸ hp.hY.continuousAt.continuousWithinAt
     filter_upwards [hp.law.filter_mono nhdsWithin_le_nhds,hX.eventually D.up,hY.eventually D.up] with i hi ha hb; rw [ha,hb,(loft t h (A:=A) (b:=b) _ _ _ hi).2,sub_self]
omit h in
lemma stemming (T:Plot μ): Uses t (StemX S H T) (D.L (StemX S H T)) A b:=by
      let W:=StemX S H T; rw [Uses]; have hp:Tendsto (W.rollX (G:=G)) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! W.rollX.continuous_of_finiteDimensional.tendsto (0:Keys G W.Free)
      exact ⟨(D.Lf W).symm ▸ D.ok.comp_tendsto hp,(D.Lw W).symm ▸ D.up.comp_tendsto hp⟩
lemma stank {p:ScriptJ (Keys G (Limb μ))}(hp:(Pond μ).Marbles p)(T:Plot μ)(U:Stir S H){P:ChartRatio G}(hk:LocalRatio P): (D.L U).pay P (U.charted (p ∘ lo_left S H G))=(Z.L T).pay P (T.charted p):=by
      let W:=StemX S H T; let q:= p ∘ lo_left S H G; rw [U.samePay W (D.waltz t h) (D.Lf _) (D.Lf _) (D.Lw _) (D.Lw _) (mpar S H hp) hk,show W.charted q=fun i=> T.charted p (prL (piBond S H T) G i) from funext fun i=> congr_arg p (beamAt S H T i)]; exact loom0 t h P T Z (D.L W) (D.stemming t T) _ (T.composeWard hp) hk
end Elm
end YM.OPE.Cascade.Rill
