import YM.OPE.Compatible.Ibis.Richer
/-! # test debts on normalized physical gauges. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d:ℕ}{n:Side}{ε v t s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea Quit.PriceZ Quit.Jac
variable {τ:Phase→ℕ}
section fee
local notation "E"=>solar G d τ
variable (p:I→ solar G d τ) (g:Filter I)(c:I→ℝ)
abbrev Alive (g:Filter I)(c:I→ℝ)(p:I→ solar G d τ):Prop:=∀ m:ℕ,∃ s:I→ℝ,RateLE g c s 0∧∀ᶠ i in g,Tide (Goan (p i)) d m (s i)
variable (n:I→Side)
noncomputable abbrev EchoΔ (K:KernelChoices)(h:4 ≤ j)(k:ℕ):= ∑ d∈ range (k+1),hikeP (Θspin K h) d 2
structure Audible (G:Gauge)(K:KernelChoices)(n:I→Side)(g:Filter I)(c:I→ℝ)(j k:ℕ)(X:I→Train j)(h:4 ≤ j)(p:∀ i, Bid.Dir G (n i) → ℝ)(s:ℝ):Prop where
       yod : ∃ r:I→ℝ, RateLE g c r s ∧∀ᶠ i in g, 0 ≤ r i ∧ Spectre (Vessel K (X i) G (n i) h) (Chart.tangent G (Body 1 (n i))) (p i) k (r i)
variable {g p c} {X:I→Train j} (h:4 ≤ j)
namespace Audible
variable {h n}
set_option quotPrecheck false
variable {p q:∀ i,Bid.Dir G (n i)→ℝ}
local notation "F"=> Audible G K n g c j k X h
lemma bigger (H:Audible G K n g c j k X h p s)(hp:s ≤ t): F p t:=by obtain ⟨b,h,he⟩:= H.yod; exact ⟨_,h.mono hp,he⟩
lemma added (H:Audible G K n g c j k X h p s)(he:Audible G K n g c j k X h q s)(ht:Tendsto c g atTop): F (p+q) s:=by
       obtain ⟨b,hb,hB⟩:= H.yod; obtain ⟨a,ha,hA⟩:= he.yod; refine ⟨fun i=>b i+a i,hb.add ha ht,?_⟩; filter_upwards [hB,hA] with i h hi; exact ⟨add_nonneg h.1 hi.1,h.2.scored hi.2⟩
lemma gauge (H:Audible G K n g c j k X h p s)(w:I→ℝ)(ht:RateLE g c w t): F (fun i=> w i • p i) (t+s):=by
       obtain ⟨b,hb,hB⟩:=H.yod; refine ⟨fun i=> ‖w i‖*b i,ht.norm.mul hb,?_⟩; filter_upwards[hB] with i hi; exact ⟨mul_nonneg (norm_nonneg _) hi.1,hi.2.weight (w i)⟩
lemma ζneg (H:Audible G K n g c j k X h p s): F (-p) s:=by
       obtain ⟨b,hb,hB⟩:=H.yod; refine ⟨b,hb,?_⟩; filter_upwards [hB] with i hi; exact ⟨hi.1,hi.2.minus⟩
lemma subtracts (H:Audible G K n g c j k X h p s)(he:Audible G K n g c j k X h q s)(ht:Tendsto c g atTop): F (p-q) s:=by rw [sub_eq_add_neg]; exact H.added he.ζneg ht
end Audible
variable {j':Phase}{z:ℕ}{w:I→ℝ}(hc:Tendsto c g atTop)(hp:Alive g c p) (a:(i:I)→Site (n i))
-- Lift.ST.R
include hp
lemma WTK (i:Phase): RateLE g c (fun j=>(p j).val i) 0:=by
       obtain ⟨s,h,he⟩:= hp (τ i); refine RateLE.of_norm_le h ?_; filter_upwards [he] with j hj; exact totalU _ (hj i)
lemma Franks (S:Aware d τ)(hw:RateLE g c w 0)(hc:Tendsto c g atTop):Alive g c (fun i=> Ripple G S (w i) (p i)):=by
       intro m; obtain ⟨s,h,H⟩:= hp m; refine ⟨fun i=>earpE (w i) (s i),(h.add ((hw.norm.mul h).mono (by norm_num)) hc).add ((((hw.pow 2 hc).norm.mul h).mono (by norm_num))) hc,?_⟩; filter_upwards [H] with i hi using Uscrew S (p i) (hi)
include hc
omit hc hp in
lemma Θpositive (K:KernelChoices)(h:4 ≤ j)(k j':ℕ)(he:0 < j'):0 ≤ hikeP (Θspin K h) k j':=by
       induction k generalizing j' with| zero=> exact zero_le_one| succ k ih=> exact mul_nonneg (spoke_pos K h _) (ih _ (by omega)) -- cmp types
lemma boomA (j':Phase): Audible G K n g c j k X h (fun i=> Rink (a i) (p i) j') 0:=by
       let q(i):= (p i).val j'; let v:=j'.val; let H:= EchoΔ K h (d+v); have he:0≤H:=sum_nonneg fun _ _=> Θpositive K h _ _ two_pos
       refine ⟨fun i=>‖q i‖*H, ((WTK hp j').norm.mul (RateLE.const _ hc)).mono (by norm_num),?_⟩; filter_upwards with i; let Q:=Rink (a i) (p i) j'; have hv:= leavesK (K:=K) (X i) h (a i) (m:=τ j') (q i); refine ⟨mul_nonneg (norm_nonneg _) he,Spectre.Ffoot (by have he:=hv 2 two_pos; rw[Finset.sum_apply] at he; simp_rw [Pi.smul_apply,smul_eq_mul, ← Finset.mul_sum] at he; exact he) hv.pu⟩
variable (S: Aware d τ)(H:Audible G K n g c j k X h (fun i=> Aview (p i) (a i) (w i)) s) (hw:RateLE g c w t)(ht: t ≤ 0)(hs:3*t≤ s)
include S H hw ht hs
lemma crest_S (j':Phase) : Audible G K n g c j k X h (fun i=>Rink (a i) (Ripple G S (w i) (p i)) j') s:=by
       let f(j:Phase)(i:I):= Rink (a i) (Ripple G S (w i) (p i)) j; let z(j:Phase)(i:I):= Rink (a i) (p i) j; have hp':∀ j:Phase,Audible G K n g c _ k X h (z j) 0:=fun j'=> boomA n h hc hp a j'; let v(i:I):=(w i)^3; have hv:RateLE g c v (3*t):=by simpa using hw.pow 3 hc
       have hh: Audible G K n g c j k X h (f 2) s:=by rw [show f 2= _ from (show f 2=fun i=>Aview (p i) (a i) (w i) from funext fun i=> (HotC ..).1)]; exact H
       have hY :Audible G K n g c j k X h (f 1) s:=by rw [show f 1=(fun i=>w i • f 2 i)-(fun i=> v i • z 2 i) from funext fun i=>(HotC (a i) (p i) S).2.1]; exact (((hh.gauge w hw).bigger (by linarith only [ht])).subtracts (((hp' 2).gauge v hv).bigger (by linarith only[hs])) hc)
       change Audible G K n g c j k X h (f j') s; fin_cases j'
       · change Audible _ _ _ _ _ _ _ _ _ (f 0) _; rw [show f 0=(fun i=>w i • f 1 i)-(fun i=>v i • z 1 i) from funext fun i=>(HotC (a i) (p i) S).2.2]; exact (((hY.gauge w hw).bigger (by linarith only [ht])).subtracts (((hp' 1).gauge v hv).bigger (by linarith only[hs])) hc)
       · exact hY
       exact hh
end fee
end YM.OPE.Ibis
