import YM.WilsonCoeffUV.Root.UV.WindowPurse
import YM.WilsonCoeffUV.Vacuum.UV.Budget
/-! # Supply engine: no use of marks after stamps to strengthen widths. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos.Polestar
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Supply Ticket
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}

abbrev frap (G:Gauge)(K:KernelChoices)(i j)(hi:4≤ i)(hj:5≤j):= (crank_fee G K.penalty K.penalty_pos (j:=j) (t:=i) (by omega) hi).choose
def knotV (G:Gauge)(K:KernelChoices)(i j)(hi:4≤ i)(hj:5≤j):= ((crank_fee G K.penalty K.penalty_pos (j:=j) (t:=i) (by omega) hi).choose_spec).choose
lemma rebate (G:Gauge)(K:KernelChoices)(i j)(hi:4≤ i)(hj:5≤j): 0<frap G K i j hi hj ∧ 0<knotV G K i j hi hj∧∀ (A:Levels G) (m N:ℕ), A.clock.kernel.penalty=K.penalty →  A.clock.J m=i →  A.clock.J (m+1)=j →  Crank (shuttleM (groove A N m)) (j-2) (frap G K i j hi hj) (knotV G K i j hi hj):= ((crank_fee G K.penalty K.penalty_pos (j:=j) (t:=i) (by omega) hi).choose_spec).choose_spec

def saffron (G:Gauge)(K:KernelChoices)(i j)(hi:4≤ i)(hj:5≤j):= min (cue G K i j hi hj).outlet (frap G K i j hi hj)
lemma safron_nn (G:Gauge)(K:KernelChoices)(i j)(hi:4≤ i)(hj:5≤j):0<saffron G K i j hi hj:= lt_min (cue G K i j hi hj).o_pos (rebate G K i j hi hj).1

def splash (G:Gauge)(K:KernelChoices)(i j)(hi:4≤ i)(hj:5≤j):= saffron G K i j hi hj /2
lemma spatter (G:Gauge)(K:KernelChoices)(i j)(hi:4≤ i)(hj:5≤j):0<splash G K i j hi hj∧ splash G K i j hi hj<saffron G K i j hi hj:=by unfold splash; exact ⟨by linarith [(safron_nn G K i j hi hj)],by linarith [(safron_nn G K i j hi hj)]⟩
-- jumps
variable {p:5≤ A.clock.J (m+1)}
private def burnt (A:Levels G)(m)(p:5≤A.clock.J (m+1)):= saffron G A.clock.kernel (A.clock.J m) (A.clock.J (m+1)) (A.clock.adm m) p
def crestM (A:Levels G)(m)(p:5≤ A.clock.J (m+1)):= splash G A.clock.kernel (A.clock.J m) (A.clock.J (m+1)) (A.clock.adm m) p
def fares (A:Levels G)(m)(p:5≤ A.clock.J (m+1)):= knotV G A.clock.kernel (A.clock.J m) (A.clock.J (m+1)) (A.clock.adm m) p
-- gap independent when T widths are equal.
def roomV (A:Levels G)(m)(p:5≤A.clock.J (m+1)) := burnt A m p/(loose A m).L.val ≤ crestM A (m+1) (upstairs A _ p)
def regionV (Ñ:ChartRatio G)(u:craftQuest A m e p)(v:roomV A m p): Bulb G:= {
    path:=(quest A m Ñ p u).gear
    input:=crestM A (m+1) (upstairs A _ p)
    s:=burnt A m p
    exitS:=crestM A m p
    preD:=fares A m p
    dept:= (rebate G A.clock.kernel (A.clock.J m) _ (A.clock.adm m) p).2.1.le
    inlet:= (spatter G A.clock.kernel (A.clock.J (m+1)) _ (A.clock.adm (m+1)) (upstairs A _ p)).1
    positive:= (spatter G A.clock.kernel (A.clock.J m) _ (A.clock.adm m) p).1
    vio:= (spatter G A.clock.kernel (A.clock.J m) _ (A.clock.adm m) p).2
    outlet:= min_le_left ..
    ports:=v }
def liftWing (Ñ:ChartRatio G)(z:h+1≤ A.clock.J (m+1)-2)(u:craftQuest A m e p)(v:roomV A m p): Cloister G h:= ⟨regionV Ñ u v, _, A.clock.J m,A.clock.adm m, A.clock.adm (m+1),by omega⟩
lemma lamplight (Ñ:ChartRatio G)(z:h+1≤A.clock.J (m+1)-2)(u:craftQuest A m e p)(v:roomV A m p): relight A Ñ m (quest A m Ñ p u) (liftWing Ñ z u v):=by
    refine ⟨rfl,?_⟩; intro N hp g b S t; rw [eq_of_heq t]; let K:=A.clock.kernel; refine ⟨destination A N m,rfl, predictionA A N m, HEq.rfl, rfl,?_⟩
    let x:= A.clock.J m; let y:= A.clock.J (m+1); exact ((rebate G K x y (A.clock.adm m) p).2.2 A m N rfl rfl rfl).mono z (min_le_right ..)

-- actual gates for e h. L.v normalized.
def underway (H:Hol G)(F:Frame G h)(pF:h<D)(e:ℕ)(I:Cloister G h):Prop:= (∀ l r, l≤ h → r≤l+e →  skulk H F pF l r I/(inkPin I).patch.L.val≤Real.exp (-Real.log (inkPin I).patch.L.val/2)) ∧ ∀ r,r≤h+e →  I.lamp.dues r
variable (H F)
lemma preSpaced (Ñ:ChartRatio G) (K:KernelChoices)(p:h<D)(e' j:ℕ): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K  →  A.clock.J (m+1)=j  → (A.S.block m).val=L  → ∀ (v:5 ≤ A.clock.J (m+1))(w:h+1≤A.clock.J (m+1)-2), roomV A m v ∧∀ (e:ℕ)(u:craftQuest A m e v)(x:roomV A m v),underway H F p e' (liftWing Ñ w u x) :=by
    have he (s x:ℝ)(hx:0<x): ∀ᶠ L:ℕ in atTop,s/L ≤ x:= by
       apply Filter.Tendsto.eventually_le_const hx (show Tendsto (fun L:ℕ=>s/L) atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    have ht (C:ℝ):∀ᶠ L:ℕ in atTop, C/L≤ Real.exp (-Real.log L /2):=by
       have H: Tendsto (fun L:ℕ=>Real.exp (Real.log L/2)) atTop atTop := Real.tendsto_exp_atTop.comp (Tendsto.atTop_div_const (by norm_num) (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
       filter_upwards [H.eventually_ge_atTop C,eventually_gt_atTop 0] with L h hL; rw [div_le_iff₀ (by positivity)]
       refine h.trans_eq ?_; nth_rw 3 [← Real.exp_log (show 0<(L:ℝ) by positivity)]; rw [←Real.exp_add]; congr 1; ring
    have hx (a b): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J m=a  →  A.clock.J (m+1)=j →  A.clock.J (m+2)=b → (A.S.block m).val=L  → ∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2), roomV A m v ∧∀ (e:ℕ)(u:craftQuest A m e v)(x:roomV A m v),underway H F p e' (liftWing Ñ w u x) := by
       by_cases hv:4≤a∧5≤j∧5≤b∧h≤j; swap
       · apply Eventually.of_forall; intro L A m z v t x h b q; exact False.elim (hv ⟨v ▸ A.clock.adm _, t▸ b,x ▸ upstairs A _ b, by omega⟩)
       obtain ⟨ha,hj,hB,hh⟩:=hv
       let s:= saffron G K a j ha hj; let i:= splash G K j b (by omega) hB
       have hu:0< i:= (spatter G K j b (by omega) hB).1; have hS:0<s:= safron_nn G K a j ha hj; let S:=knotV G K a j ha hj
       let B:= (licence H F p K.penalty_pos (show 4≤ j by omega) ha hh hu).choose
       let z v r:= shadesT F v*B*tempS H F r p i s S hu hS
       let E:= Finset.range (e'+h+1); let P:= Finset.range (h+1)
       filter_upwards [ (eventually_all_finset P).mpr (fun v _=> (eventually_all_finset E).mpr (fun r _=> ht (z v r))), (eventually_all_finset E).mpr (fun r _=> he ((r:ℝ)*s) (i/2) (by positivity)), he s i hu] with l hl hp hK
       intro A m he v t hx hy H' hh
       subst K a j b l
       exact ⟨hK,fun e u q=> ⟨fun i j hi hj=>hl _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega)),fun r g=>by
          unfold Bulb.dues; rw [←mul_div_assoc]; exact hp _ (Finset.mem_range.mpr (by omega))⟩⟩
    let S:= Finset.range (j+2)
    filter_upwards [ (eventually_all_finset S).mpr (fun a _ => (eventually_all_finset S).mpr (fun b _=>hx a b))] with L hL
    intro A m p q z h b; have hS:A.clock.J (m+2)≤A.clock.J (m+1)+1:= A.fits.stepSlow (m+1); have hp:A.clock.J m≤ A.clock.J (m+1):= A.fits.mono m.le_succ; exact hL _ (show A.clock.J m∈S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m p rfl q rfl z h b
end YM.WilsonCoeffUV.Cosmos.Polestar
