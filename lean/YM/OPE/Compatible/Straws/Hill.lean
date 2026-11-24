import YM.OPE.Compatible.Straws.Raise
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift Glass
variable {F:Fiber E G I}{X Y:Path E G D}{p:Keys G D→ℝ}(Z:F.SeriesUp X p)(B:F.SeriesUp Y p) {P:ChartRatio G}(R:LocalRatio P)
local notation "ν0"=> camp F X
local notation "μπ"=> Chart.tangent G D
local notation "ωμ"=> Chart.tangent G I
local notation "JΘ" => crossT ωμ F.Q
local notation "μ0"=> cloth F P
def predicts (A:Fiber E G I)(P:ChartRatio G)(q:ScriptJ (E× Keys G I))(x:E):Token:= let p:= A.cloth P; (crossT ωμ A.Q ((q ∘ drape E Y! A.M)*p) x)/(crossT ωμ A.Q p x)
include R
omit [BorelSpace E] in lemma cloth_B : ScriptJ.B μ0:=fun i=> (curlingB F.H (F.signB R) i).compLinear (drape E Y! F.M).toLinearMap -- include
omit [BorelSpace E] in lemma veil (u:E): ((JΘ μ0) u).s=1:=headD _ _ _ fun _=> Adhesion.curT (h:= F.signPay R) _
omit [BorelSpace E] in lemma predictB (q:ScriptJ (E× Keys G I))(hp:q.B): ScriptJ.B (F.predicts P q):=by
      let s:E×Y!→Token:= μ0; let h:=cloth_B (F:=F) R; let U:=drape E Y! F.M; let A:=q∘U; have hh:ScriptJ.B A:=fun i=>(hp i).compLinear U.toLinearMap; let D:=JΘ s; let T:E→Token:= fun x=>(D x)⁻¹; have ht: ScriptJ.B T:= mintInv D (crossB _ _ _ h) (fun i=> veil R i); exact ScriptJ.height (p:=JΘ (A*s)) (crossB _ _ _ (ScriptJ.height hh h)) ht
namespace SeriesUp
variable {Ω:Dimes G (D ⊕ I) (D ⊕ I)}
include R
omit [BorelSpace E] in
lemma arisen (u:U!)(q:ScriptJ (E×Y!))(hp:q.B):
      mine (F.predicts P q ∘ X.timber u)=(Z.netJet P (Caul X q) u)/(Z.netJet P 1 u):=by
          let s:E×Y!→Token:= μ0; let d:= Z.netJet P 1 u; let Q:=JΘ s; let v:=drape E Y! F.M; let A':=q∘v; let A:= JΘ (A'*s); let C:= X.timber u; let k:=trill fun i=> Z.horsa u i P; have hv:=JewelA (F:=F) (X:=X) u _ (cloth_B R) (fun x=>curT (F.signPay R) (v x)); have he:(Z.seedOne P).s=1:= seedBase Z R
          let β:=(Z.seedOne P)⁻¹*k; have hb:β.s=1:=by change ((Z.seedOne P)⁻¹*k).s=1; rw [ml_s,show k.s=1 from costs0 u Z R,sp_s, he,inv_one,mul_one]
          have ha: Z.netJet P (Caul X q) u= β*mine (A ∘ C) :=by unfold netJet dessert; rw [jewelry u Z R q hp, ←mul_assoc];rfl
          have hl:d=β*mine (Q ∘ C):=by unfold d netJet dessert; rw [one_mul,jewelVac u Z R,← mul_assoc]; rfl
          rw [ha,show Z.netJet P 1 u=_ from hl, JetS.transfer _ _ _ (hb.trans_ne one_ne_zero) (show (mine (Q ∘ C)).s ≠ 0 from ((show (mine (Q ∘ C)).s=1 from hv).trans_ne one_ne_zero)), dv]
          have hu:ScriptJ.B A':= fun i=>(hp i).compLinear v.toLinearMap; have hs:= Timber X u; let c: ℝ→Token:= fun i=>(Q (C i))⁻¹; have hF:ScriptJ.B Q:=crossB _ _ _ (cloth_B R); change mine ((A ∘ C)*c)= _;rw [Fitted.slopes (p:=A ∘ C) (q:=c) (Fitted.arose C A hs (crossB _ _ _ (ScriptJ.height hu (cloth_B (F:=F) R)))) (Fitted.arose C _ hs (mintInv Q hF (fun x=> veil R x)))]; exact congr_arg _ (Fitted.verse (Q ∘ C) (Fitted.arose C _ hs hF) (fun x=> veil R _))
omit [BorelSpace E] in lemma Saga (K:Raiser Z B Ω)(q w:ScriptJ (E×Y!))(hq:q.B)(hw:w.B)(h:Ω.pulse (Caul X q) (Caul Y w))(u:U!):
      (jur (F.predicts P q ∘ X.timber u) - jur (F.predicts P w ∘ Y.timber u)) =O[Lf](gradeP 3):=by
           let v:= F.predicts P q; let W:= F.predicts P w; have hz:= optic Z B R K _ _ (caulB _ _ hq) (caulB _ _ hw) h; have hb:= optic Z B R K 1 1 (Bfray (E:=K!) _) (Bfray _) (fun i=> Reads.selves _); let x:= v ∘ X.timber u; let y:= W ∘ Y.timber u; have H: mine x=mine y:=by unfold x v y W; rw [arisen Z R u q hq, arisen B R u w hw,hz,hb]
           have hx:Fitted x:= Fitted.arose (X.timber u) v (Timber _ _) (predictB R _ hq); have hy:Fitted y:= Fitted.arose (Y.timber u) W (Timber _ _) (predictB R _ hw); change (jur x- jur y)=O[Lf](gradeP 3); rw [show jur x-jur y=(jur x-(mine x).atK)-(jur y-(mine y).atK) by rw [H]; abel]; exact (hx.take).sub (hy.take)
end SeriesUp
end Fiber
end YM.OPE.Libra
