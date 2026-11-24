import YM.OPE.Compatible.Arch.Ear
/-!
# Through the entire arc of a gauge. Used also in auxiliary torus identities. Includes marks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision OPE.Libra
variable {G:Gauge}
local notation "Lf" => Tested.germ
namespace Score
variable {D V:Type}[Fintype D]{B:Set V}
variable (R:Score D V)
-- Taylor invariance condition through any analytic arcs x(ξ),y(ξ),g(ξ). Need restriction group Color via log, allow limit global constant later.
structure Track (x y:ℝ→ Keys G D)(s:ℝ→ Tile G V): Prop where
   hX : ContDiffAt ℝ ∞ x 0
   hY : ContDiffAt ℝ ∞ y 0
   gx : x 0=0
   gy : y 0=0
   law : ∀ᶠ t in 𝓝 0, R.dress (s t) (put (x t))=put (y t)
   chart (v:V): ContDiffAt ℝ ∞ (fun t=>G.mat (s t v)) 0
-- unrestricted s(0) stabilized by law (connected graph), no boundary assumptions. 
structure Walks (f w:Keys G D→ℝ):Prop where
   sane : ContDiffAt ℝ ∞ f 0
   warm : ContDiffAt ℝ ∞ w 0
   reel {x y:ℝ→ Keys G D}{s:ℝ→Tile G V}(h:R.Track x y s): ((fun t:ℝ=> (f (x t)-f (y t))/t^2): ℝ→ℝ)=O[Lf](Libra.gradeP 3)
   wax {x y:ℝ→ Keys G D}{s:ℝ→Tile G V}(h:R.Track x y s): ((fun t:ℝ=> w (x t)-w (y t)):ℝ→ℝ)=O[Lf](Libra.gradeP 3)
protected structure Marbles (p:ScriptJ (Keys G D)):Prop where
   toll: p.B
   honors {x y:ℝ→ Keys G D}{s:ℝ→ Tile G V}(h:R.Track x y s): ((fun t:ℝ=> (p (t⁻¹ • x t)).atK t-(p (t⁻¹ • y t)).atK t):ℝ→ℝ)=O[Lf](Libra.gradeP 3)
namespace Stand
variable {R}
variable (T H:R.Stand B)
lemma sphere : ∀ᶠ x:Tile G D in 𝓝 1,put (unput x)=x:=by
    have hh(i:D): ∀ᶠ x:Tile G D in 𝓝 1, G.lieExp (unput x i)=x i:= (show Tendsto (fun x:Tile G D=> x i) (𝓝 1) (𝓝 1) from (continuous_apply i).continuousAt).eventually (p:=fun x:G.El=> G.lieExp (G.plog (G.mat x))=x) G.plog_right
    filter_upwards [eventually_all.mpr hh] with x hx using funext hx
def juggle (x:Keys G T.Free)(t:ℝ) := H.sweep (put (T.rollX (t•x)))
local notation "Φ" => beenX (G:=G) T H
lemma acorn (u:Keys G T.Free): R.Track (fun t:ℝ=>T.rollX (t • u)) (fun t:ℝ=>H.rollX ((beenX T H).gradient (t • u))) (T.juggle H u) := by
    let A:=T.beenX (G:=G) H; let k(t:ℝ):= t • u
    let w: Keys G T.Free→ Tile G H.Free:= fun x=> A.q (put x)
    have hk : ContDiffAt ℝ ω k 0:= contDiffAt_id.smul contDiffAt_const
    have hw:Tendsto w (𝓝 0) (𝓝 1):=by unfold w; simpa only [Function.comp_apply,put_zero, A.clan] using! (A.q.continuous.comp putC).tendsto (0:Keys G T.Free)
    have Hf:∀ᶠ t:ℝ in 𝓝 0, put (A.gradient (t • u))=w (t • u) :=by
         have h : Tendsto k (𝓝 0) (𝓝 0):= by simpa [k] using! hk.continuousAt.tendsto
         have he: (∀ᶠ t:ℝ in 𝓝 0,put (unput (w (t • u)))=w (t • u)):= (hw.comp h).eventually (p:=fun x=>put (unput x)=x) sphere
         filter_upwards [h.eventually A.lead_grad, he] with x hn hz; change A.gradient (x • u)=_ at hn; rw [hn]; exact hz
    refine ⟨(toContinuousLinearMap T.rollX|>.contDiff|>.contDiffAt).comp 0 (hk.of_le le_top),(show ContDiffAt ℝ ∞ (H.rollX ∘ A.gradient ∘ k) 0 from (toContinuousLinearMap H.rollX|>.contDiff|>.contDiffAt).comp 0 ((show ContDiffAt ℝ ∞ A.gradient (k 0) from by simp only [k, zero_smul]; exact A.gradC).comp (g:=A.gradient) (f:=k) 0 (hk.of_le le_top))),by simp,by simp,?_,?_⟩
    · filter_upwards [Hf] with t h; unfold juggle; rw [H.rollPut,h,H.emits]; rw [T.rollPut];rfl
    intro i; exact (H.sweptLog (i:=0) (u:=fun t:ℝ=> put (T.rollX (t•u))) (fun j=> (paintD ..).comp 0 ((toContinuousLinearMap T.rollX |>.contDiff|>.contDiffAt).comp 0 hk)) i).of_le le_top
-- apply currency
abbrev charted (p:ScriptJ (Keys G D)) : ScriptJ (Keys G T.Free):= p ∘ T.rollX
lemma composeWard {p:ScriptJ (Keys G D)} (h:R.Marbles p): (T.charted p).B:= fun i=> (Libra.Bond.compLinear T.rollX (h.toll i))
lemma polished {K:Lid G T.Free}{L:Lid G H.Free}{f w:Keys G D→ℝ}(hw:R.Walks f w)(hK:K.f=f∘T.rollX)(hL:L.f=f∘H.rollX)(hU:K.w=w∘T.rollX)(hV:L.w=w∘H.rollX): Dimes.Mint (T.beenX H) K L := by
     constructor
     · intro u; have he : Reads (fun t:ℝ=> K.f (t • u)/t^2) (Pawn.mold K.f 2 u):=(Pawn.trio K.F).stale _
       have hp:= hw.reel (T.acorn H u); unfold Reads
       convert! IsBigO.sub he hp using 2; simp only [Pi.sub_apply]; rw [hK,hL]; simp only [_root_.Function.comp_apply]; ring -- morph
     intro u; have he : Reads (fun t:ℝ=> K.w (t•u)) (Pawn.mold K.w 0 u):=(Pawn.calm K.coat).stale _; have hp:= hw.wax (T.acorn H u); unfold Reads; convert! IsBigO.sub he hp using 2; simp only [Pi.sub_apply]; rw [hU,hV]; simp
lemma polishedP {p:ScriptJ (Keys G D)}(ht:R.Marbles p): (T.beenX H).pulse (T.charted p) (H.charted p):=by
     intro u; have hv:= ht.honors (T.acorn H u); unfold Reads; apply hv.neg_left.congr' _ Filter.EventuallyEq.rfl; filter_upwards [Tested.eventually_pos] with t (hT:0<t); simp only [← map_smul H.rollX,map_smul T.rollX]; rw [inv_smul_smul₀ hT.ne']; simp [charted]
lemma samePay {K:Lid G T.Free}{L:Lid G H.Free}{f w:Keys G D→ℝ}(hw:R.Walks f w)(hK:K.f=f∘T.rollX)(hL:L.f=f∘H.rollX)(hU:K.w=w∘T.rollX)(hV:L.w=w∘H.rollX){p:ScriptJ (Keys G D)}(ht:R.Marbles p){P:ChartRatio G}(Gd:LocalRatio P): K.pay P (T.charted p)=L.pay P (H.charted p):= Dimes.congr_charge _ ((T.polished H hw hK hL hU hV).borders) (H.composeWard ht) (T.polishedP H ht) Gd
end Stand
end Score
end YM.OPE.Cascade
