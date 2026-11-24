import YM.OPE.Compatible.Grafts.Adv
/-!
# Ordinary and quotient paths. Poles
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)
local notation "X!"=> forest S.ratio he
local notation "Z!" => AxisChart G X!
local notation "K!" => Bid.Dir G c
local notation "U!" => Bid.Dir G f
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable {P:ChartRatio G}(ht:LocalRatio P)
open Flume.Script Shell Char Pilot
open Planned.PrimaryIntegral295.Carrier
lemma spineP (Q:Patch)(L:KernelChoices)(D: Boxes G Q L):∃ s b:ℝ,0<s ∧0 ≤ b∧ D.dot.strip s b∧ (ROOT (I:=Shade G) D.dot).strip s b ∧ D.main.strip s b∧ (marry D.main).strip s b:=by
      obtain ⟨s,b,hp,hb⟩:= D.rocket1; obtain ⟨t,g,ht,hG⟩:= root_cash (I:=Shade G) D.dot D.rocket1; obtain ⟨u,c,hU,hc⟩:= D.rocket2; obtain ⟨v,w,hv,hw⟩:= payact D.main D.rocket2
      exact ⟨min (min s t) (min u v), max 0 (max (max b g) (max c w)),lt_min (lt_min hp ht) (lt_min hU hv),le_max_left ..,strip_mono hb (by grind) (by grind), strip_mono hG (by grind) (by grind),strip_mono hc (by grind) (by grind), strip_mono hw (by grind) (by grind)⟩
variable (p:ChartRatio G) (Q:Patch) (k m n':ℕ)
lemma gaV (Q:Patch)(k:KernelChoices)(A:Alps K T i v)(p:ChartRatio G)(b:ℝ)(m:ℕ):∃ z:ℝ, 1 ≤ z ∧ weightsB (novel Q k v i A b p) m (fun _=>z):=by
       let C:StepData 1 (1*Q.L):= ⟨Q,k,rfl⟩; obtain ⟨ha,hb,hc⟩:= tide_feed C (A:=A) b p; obtain ⟨u,hu⟩:=ha m; obtain ⟨v',hv⟩:=hb m; obtain ⟨w,hw⟩:=hc m; let z:=max 1 <| max u (max v' w); have hV:= Sack.tips hv (show v'≤z by grind); have hW:= Sack.tips hw (show w ≤ z by grind); have hU:= Sack.tips hu (show u ≤ z by grind); refine ⟨z,le_max_left ..,fun i=>?_⟩; fin_cases i
       · exact hV
       · exact hV
       · exact hW
       · exact hU
       -- p4? Paloma
       exact Sack.zero (le_trans zero_le_one (le_max_left ..)) _
-- specialized uniform. `studio` @ code
abbrev subStud (Q:Patch)(k:KernelChoices)(n:Side):StepData n (n*Q.L) :=⟨Q,k,rfl⟩
section cap
variable (Q:Patch)(hs:G.Simple)(hc:k+44≤m)(α B:ℝ)(hα:0<α)(hB:0 ≤ B)
structure Telet {C: KernelChoices} (D:Boxes G Q C)(a b:ℝ):Prop where
    dot: D.dot.strip a b
    full: (ROOT (I:=Shade G) D.dot).strip a b
    main: D.main.strip a b
    marr: (marry D.main).strip a b
abbrev TracePay (S:StepData c f)(he:Odd S.ratio.count.val)(U:Boxes G S.patch S.kernel)(A: Alps K T i v)(t:S.Choices)(g: Bid.Dir G c→AxisChart G (forest S.ratio he))(p: ChartRatio G)(d:ℕ)(Q:Muse G)(b:ℝ)(a:Site c)(X:FibreRep S he U t A g b): ScriptJ (Bid.Dir G c):= X.L.predicts p ((inkM Q d (S.ratio.embed a)) ∘ ribz S he) -- ambiguity names.s
include hs hc hα hB
lemma costsS (K:Sponsor G)(T:Seasons K)(P:ChartRatio G)(R:LocalRatio P)(C:KernelChoices)(i d:ℕ):∃ D:ℝ,0 ≤ D∧ ∀ n: Side,∀ (A: Boxes G Q C), Telet Q A α B →∀ (v b:ℝ)(X:Alps K T i v)(L g), licensed (subStud Q C n) Q.odd_side A X.clip X.live L X.sky g→∀ (t:(subStud Q C n).Choices)(U:FibreRep (subStud Q C n) Q.odd_side A t X g b)(x:Site n)(V:Muse G)(f:ℝ), Tide V d m f → ∀ w:ℝ,1 ≤ w → weightsB (novel Q C v i X b P) m (fun _=> w) →
         Tide (rushS Q C X b A P V d) d m (D*w^5*f)∧ ∀ (y:Bid.Dir G n)(j:Phase), Mold ((TracePay (subStud Q C n) Q.odd_side A X t g P d V b x U y).seq j.val) ((inkM (rushS Q C X b A P V d) d x y).seq j.val) (D*w^5*f*(1+‖spool G n y‖)^glideZ d) n k:=by
        let I:= Script.Tile G Q.L; let C'(k):=widthCost α k*B; obtain ⟨σ,hσ,h⟩:= prisms (I:=I) d m k α B C' hα hB (fun i=>mul_nonneg (zero_le_one.trans (widthCost_ge hα i)) hB) hc; obtain ⟨a,b,hA,hb⟩:= drip_cash G Q.L
        let T':= costD I (size (0:Cover)) m b a (d+2); let W:= costD (Shade G) (size (0:Cover)) m B α (d+2); let x:=Fintype.card (Shade G)*B; let R1:= σ*T'*W; let R2:= σ*T'*(x+1)^glideZ d
        have hu:0 ≤ T':=costD0 ..; have hv:0 ≤ W:=costD0 ..; refine ⟨max R1 R2,(show 0 ≤ R1 by unfold R1; positivity).trans (le_max_left ..),?_⟩; intro n D hT v b' X L g hx t U p V f hh w hw hW; let S:=subStud Q C n; let he:=Q.odd_side; let M:= mintR S X P b'; let Φ(y:Bid.Dir G n):= D.main.acts n *ᵥ spool G n y; let Ξ:=Piax S G D; let F:= branchOut Q G V; let K' := meld Q C X b' D P V d; let Y:=f*T'
        have he'(y:Bid.Dir G n): Φ y= dance S Q.odd_side G (fieldT (cabin g) y):=(bounty S _ D t hx y).symm; let K1:= Chart.tangent G (forest S.ratio he).Free; let Z:=AzLight S he G; have hg: Tide F d m Y:= rebound (drip G Q.L) 0 _ a b _ _ _ hb hA hh; have hC:=hW
        have hy(y:Bid.Dir G n) := h n _ K1 U.L.Q Ξ hT.full M 1 (Φ y) Z p (scopeT S he D t hx U α B hα hB hT.dot P (Φ y) p m) w hw hC _ Y hg; obtain ⟨hq,-⟩:=hy 0; have hY: Tide K' d m (σ*w^5*Y):=hq; have hf :0≤f:= Sack.coins ((hh 0).2 0)
        constructor
        · intro j; have hd: R1*w^5*f≤ max R1 R2*w^5*f:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)) hf; refine ((rebound _ 0 K' α B _ _ _ hT.marr hα hY j).raise _ le_rfl ((le_of_eq ?_).trans hd)); change σ*w^5*(f*T')*W=_; unfold R1; ring
        intro y j; let Ψ:=inkM V d (S.ratio.embed p); have hr:inkM (rushS Q C X b' D P V d) d p y=Libra.Char.go K' d (Φ y) p:= sameSide n p d Q K' (filament _ _ hY) _ _ D.rocket2
        let ξ:=TracePay S he D X t g P d V b' p U y; have hm: fair K1 U.L.Q (Stell (Libra.Char.Sketch M 1 (Φ y) Z)) (cups F d p (Φ y) Z) = ξ:=by rw [he']; exact rawFare S he D t hx R (filament f V hh) hs p U y
        rw [hr]; change Mold (ξ.seq j.val) _ _ _ _; rw [←hm]; apply ( (hy y).2 j).trans; change σ*w^5*Y*(1+‖Φ y‖)^glideZ d ≤ _ ; let U':=1+‖spool G n y‖; have hX: 0≤ x:=by unfold x; positivity
        have hh' :1+‖Φ y‖≤ (x+1)*U':=by
             let a:=spool G n y; have ht: ‖Φ y‖≤x*‖a‖:=vape α B D.main hT.main hα.le hB a; apply le_trans (add_le_add_right ht 1); change 1+x*‖a‖≤ (x+1)*(1+‖a‖); rw [show (x+1)*(1+‖a‖)=1+x*‖a‖+(x+‖a‖) by ring]; exact le_add_of_nonneg_right (add_nonneg hX (norm_nonneg _))
        refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ 1+‖Φ y‖ by positivity) hh' _) (show 0 ≤ σ*w^5*Y by unfold Y;positivity)).trans ?_; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right R1 R2) (pow_nonneg (zero_le_one.trans hw) _)) hf) (show 0≤U'^glideZ d from pow_nonneg (show 0 ≤ U' by unfold U'; positivity) _)); rw [mul_pow]; unfold Y R2; apply le_of_eq;ring
end cap
end YM.OPE.Cascade.Rill
