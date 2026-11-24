import YM.OPE.Compatible.Melon.Kraft
/-!
# Feynman gauge identity < quadratic ξ. Quantified at each regulator. Costs attached later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {A:Alps B Q i l} {H: Even n.val}
local notation "Lf" => Tested.germ
local notation "TK" => Keys G (Limb H)
variable (T:Plot H) (X:Lit H A b) (R:Bor H A b)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
local notation "W" => Chart.tangent G T.Stable
local notation "Tμ" => Chart.tangent G T.Free
local notation "Pμ" => Chart.tangent G (Limb H)
variable {P:ChartRatio G} (V:LocalRatio P)
open ScriptJ
abbrev Homog (p q: Token) :=p.s=q.s∧p.l=q.l
include V
lemma jointP (p:ScriptJ FD)(h:4 ≤ i)(hv:G.Simple)(hp:p.B): Homog
    (draw ((ballow T X h).hat P * (p∘ (T.slab G))) (penon (ballow T X h)) Pμ) (draw ((R.L T).hat P*p) (penon (R.L T)) Tμ) := by
      let L:= penon (R.L T); let u:=ballow T X h; let Y:=u.hat P; let Q:= fond H T G; let M:=compass H T G; let f:ScriptJ TK:= Y * (p ∘ T.slab G); let g:ScriptJ FD:= (R.L T).hat P * p; change Homog (draw f _ _) (draw g _ _)
      have hf:f.B:= ScriptJ.height (u.hat_toll V) (fun i=> (hp i).compLinear (T.slab G).toLinearMap)
      have ha {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F](μ:Measure E)[μ.IsAddHaarMeasure](ν:Measure F)[ν.IsAddHaarMeasure] :(μ.prod ν).IsAddHaarMeasure:=inferInstance
      let m:Measure (FD×DK):=(Tμ).prod W
      haveI hm:m.IsAddHaarMeasure:=ha Tμ W
      have he:= ease f hf M.symm (penon u) (united L Q) (fun x=>by convert jointW T X R (M.symm x) h using 2 <;> simp [M,u]) Pμ m
      have hB : ScriptJ.B (f ∘ M) := fun i=> (hf i).compLinear M.toLinearMap; rw [he]; constructor
      · change (united L Q).average ((Tμ).prod W) (fun v:FD×DK=>(f (M v)).s) = _; rw [harvested Tμ W L Q (fun v:FD×DK=>(f (M v)).s) (hB 0)]; apply congr_arg (L.average Tμ); funext i; change Q.average W (fun y:DK=>(f (M (i,y))).s)= (g i).s; simp only [f,M,g, Pi.mul_apply, JetS.ml_s,Y,u, Function.comp_apply, firstC, Lid.hat_full _ V]; exact singleConst ..
      change (united L Q).average ((Tμ).prod W) (fun v:FD×DK=>(f (M v)).l) = _; rw [harvested Tμ W L Q (fun v:FD×DK=>(f (M v)).l) (hB 1)]; apply congr_arg (L.average Tμ)
      funext i; change Q.average W _= (g i).l; let z:DK→ℝ:=fun y=>jet (tall T) 3 (M (i,y))
      rw [show (fun x:DK=>(f (M (i,x))).l)=(fun _=>(g i).l)+(-(p i).s • z) from funext fun x=> by simp only [f,M,g, Pi.mul_apply, JetS.ml_l, Y,u,Function.comp_apply,firstC, Lid.hat_full _ V, Pi.smul_apply,smul_eq_mul,Pi.add_apply,hotRead T X R V i x h]; unfold z M; ring]
      rw [sun W Q (Bond.keep _) (Bond.scale _ (wingBond T i)), singleConst, scooted,show Q.average W z=0 from quenching T i hv]; ring
lemma capsule (p:ScriptJ TK)(h:4≤ i)(hv:G.Simple)(hp:(Pond H).Marbles p): Homog (X.s.pay P p) ((R.L T).pay P (T.charted p)):=by
      rw [bornPaid T X P V p hp h]; let Z:= ballow T X h; let f:=T.charted p; let g:ScriptJ TK:= f ∘ T.slab G;let C:=R.L T
      change Homog (Z.pay P g) (C.pay P f); rw [Z.cutOut V _ g (penon_shape Z), C.cutOut V _ f (penon_shape C)]; rw [mul_comm g,mul_comm f]
      obtain ⟨hr,hY⟩:= jointP T X R V f h hv (T.composeWard hp); have he: Homog (draw (Z.hat P) (penon Z) Pμ) (draw (C.hat P) (penon C) Tμ):=by
         have ht: ((1:ScriptJ FD) ∘ T.slab G)=(1:ScriptJ TK):=rfl
         simpa only [Z,C,ht,mul_one] using jointP T X R V (1:ScriptJ FD) h hv (Xbond Bond.one Bond.zero Bond.zero)
      obtain ⟨he,hh⟩:=he; change (draw (Z.hat P*g) _ _).s=_ at hr; change (draw (Z.hat P*g) _ _).l=_ at hY; simp only [Homog, JetS.dv, JetS.ml_s,JetS.ml_l,JetS.sp_s,JetS.sp_l]; rw [hr,hY,he,hh]; exact ⟨rfl,rfl⟩
end YM.OPE.Cascade.Glass
