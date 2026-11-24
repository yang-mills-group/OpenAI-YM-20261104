import YM.MSbar.Domain.Volume

/-! Hat continuation integrated amplitude at any supported symbol cut. Choose directions
Mars; sign bookkeeping may be paid separately; no phantom epsilon factors here except measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Dim Symbol Super Loops MeasureTheory Function Set Filter Metric Complex
open scoped Topology BigOperators Classical ContDiff ENNReal
namespace DR
variable {T:ℕ→Type}{S:Site T} {m n j:ℕ} {U:Set ℂ}{K:ℝ}{F : Record (fun m=> T m × Mom m)}

-- horizontal *static* integral over a compact parameter
lemma deposit {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] {G:Record (fun m=> T m × E)}
    (h:Eligible U j (S.prod (Site.simple E)) G) (μ:Measure E)[IsLocallyFiniteMeasure μ] (hu : IsOpen U) {X:Set E}(hh:IsCompact X) : Eligible U j S (fun z n x=> ∫ t in X,G z n (x,t) ∂μ):=by
    refine ⟨fun z hz ⦃i n⦄ P x=> ?_,?_⟩
    · exact integral_congr_ae (Eventually.of_forall fun t=> h.natural z hz P (x,t))
    intro D i1 i2 i3 m p hp
    have hc:= h.ev _ (fun t:D × E=>(p t.1,t.2)) (show (S.prod (Site.simple E)).plot _ from ⟨S.views (p:=Prod.fst) hp tame_projL,tame_projR⟩)
    let g(x:ℂ × (D × E)):= G x.1 m (p x.2.1,x.2.2); change Bet U j g at hc
    haveI:IsFiniteMeasure (μ.restrict X):= ⟨by rw [Measure.restrict_apply_univ]; exact hh.measure_lt_top⟩
    have hd:=hc.cost.after_average (μ:=μ.restrict X) (p:=id) (integrable_const (1:ℂ)) aestronglyMeasurable_id (ae_restrict_mem hh.measurableSet) hh
    exact ⟨by simpa [g,id] using hd,fun h=>Transfer.Market.average hh (hc.gains h)⟩

-- moment-space localized support condition.
structure Situated (U:Set ℂ)(j:ℕ)(S:Site T)(K:ℝ)(F:Record (fun m=>T m×Mom m)):Prop where
    suit: Eligible U j (S.prod momentum) F
    pays (z : ℂ) : z∈U → ∀ i (x:T i), let g:=fun v : Mom i=> F z i (x,v); g.HasTemperateGrowth ∧ Vanish K g
    nn : 0≤ K

def sumP (S:Motion T)(z:ℂ)(F:∀ m,T m × Mom m→ℂ) (m:ℕ)(p:T m × Bar):= request (S.prod (constMotion Bar)) (fun m x=>F m (x.1.1,x.1.2,x.2)) z m p
def turn (S:Motion T) (z:ℂ)(F:∀ m,T m × Mom m→ℂ) (m:ℕ)(x:T m):= measure z* ∫ u,sumP S z F m (x,u)
def loop (S:Motion T)(F:Record (fun m=>T m × Mom m)) : Record T:= fun z=> turn S z (F z)

namespace Situated
variable (h: Situated U j S K F) {z:ℂ} (hz:z∈U)

private def into : Draw (((S.prod (Site.simple Bar))).prod Site.moving) (S.prod momentum) (fun m x=>(x.1.1,x.1.2,x.2)):=
    ⟨fun _ _ => rfl,by introv H; exact ⟨H.1.1,H.1.2,H.2⟩⟩
include h hz
lemma round (x:T m)(u: Bar): Packed m K (fun v=> F z _ (above S.toMotion x,(u,v))) := by
    let A:= S.prod (Site.simple Bar); obtain ⟨hG,hK⟩:= h.pays z hz (m+1) (above S.toMotion x); have hh:= (h.suit.arg (into (S:=S))).natural z hz
    exact Tower.prepares hh (x,u) h.nn (fun v hv=> hK (u,v) (hv.trans_le (le_max_right ..))) (hG.1.comp (contDiff_const.prodMk contDiff_id))
lemma ends (x:T m): Vanish K (fun v=> sumP S.toMotion z (F z) m (x,v)):= by
    intro v hv; unfold sumP request; change plate z (fun u: Hat (m+1)=>F z (m+1) (above S.toMotion x,v,u))=0
    rw [show (fun u:Hat (m+1)=> _)=(0:Hat (m+1)→ℂ) from funext (fun u=> (h.pays z hz _ _).2 (v,u) (hv.trans_le (le_max_left ..))),plate_zero]
omit hz in
lemma costs (hu : IsOpen U) : Eligible U (1+j) S (loop S.toMotion F) := by
    have hA: Eligible U (1+j) (S.prod (Site.simple Bar)) (fun z=> sumP S.toMotion z (F z)) := (h.suit.arg (into (S:=S))).plate K hu (fun z hz i x=> h.round hz x.1 x.2)
    let P:=closedBall (0:Bar) K
    have he:= (DR.worth (S:=S)).mul (deposit hA volume hu (show IsCompact P from isCompact_closedBall ..))
    rw [zero_add] at he; refine he.agrees hu fun z hz=>funext (fun m=> funext (fun x=>?_))
    unfold loop turn; rw [Vanish.face (h.ends hz x)];rfl

-- physical integer value at full actual measure
omit hz in
lemma integer {m:ℕ}(hz:(m:ℂ)∈U)(x:T m) : loop S.toMotion F m m x = ∫ v,F m m (x,v) ∂ (ENNReal.ofReal (mass m) • volume: Measure (Mom m)) := by
    rw [loop,turn,measure_nat]; let g(v:Mom m):=F m m (x,v)
    rw [integral_smul_measure]; have hm := mass_pos m
    simp only [ENNReal.toReal_ofReal hm.le]; change _=(↑(mass m):ℂ)*(∫ v,g v ∂Measure.prod volume volume);rw [integral_prod]; congr! 1; apply integral_congr_ae
    · filter_upwards with v; change sumP _ _ _ _ _ = _; exact Tower.canonical ((h.suit.arg (into (S:=S))).natural m hz) (x,v) (h.round hz _ _)
    exact ((h.pays _ hz _ x).1.1.continuous).integrable_of_hasCompactSupport ((h.pays _ hz _ x).2.compact)
end Situated
end DR
end YM.MSbar.Domain
