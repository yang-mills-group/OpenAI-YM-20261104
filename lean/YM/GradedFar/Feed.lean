import YM.GradedFar.Labor
/-!
# Physical payment, moving frames. All coordinates actual.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Filter Finset Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2.GradedFar
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (Jp:ℝ→tower S)
    {I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ} {A B:Type*}{t:Filter A}{U:A→B→Prop}
    {M δ:ℝ}{P:A→B→Purchase F I J} {s L W:A→B→ℝ}
    (l:Labor M δ t U L s P) (hG:G.Simple) (Ht:LogTrace F R.port)
    (Hw:∀ i,Coat F R Jp (d i))(Hw':∀ i,Coat F R Jp (e i))
    {u:A→B→WholeInput G d}{v:A→B→WholeInput G e}
    (hu:∀ᶠ a in t,∀ z i,U a z → width (u a z i) ≤ 1)
    (hv:∀ᶠ a in t,∀ z i,U a z → width (v a z i) ≤ 1)
local notation "Scene" => Purchase F I J
local notation "gapₗ" => Sold t U L
local notation "Ok" => Safe t U L
local notation "wₗ" => fun a z=> moved Jp (s a z) (v a z)
local notation "u₁" => fun a z=> moved Jp (smallLength P a z) (u a z)
local notation "xₗ" => fun (a:A) (z:B)=> Purchase.head (P a z)
local notation "oₗ" => fun (a:A) (z:B)=> Purchase.center (P a z)
local notation "yₗ" => fun a z=> Purchase.tail (P a z) (s a z)
local notation "Vₗ" => fun a z=> spectator F (Purchase.viewer (P a z))
include l
omit [Fintype I] [Fintype J] in
lemma Labor.properO (hq:∀ᶠ a in t,∀ z,U a z→ 0 ≤ W a z):Safe t U L W :=
  (l.tiny.logs.and hq).mono (fun _ h z he=>⟨h.1 z he,h.2 z he⟩)
omit [Fintype I] [Fintype J] in
lemma Labor.properS :Safe t U L s:= l.properO F (l.large.pos.mono fun _ h z he=> (h z he).le)

omit l
def tariff (h:ℕ)(r s: A→B→ℝ)(a:A)(z:B):=s a z+(r a z/s a z)^(h+1)
include l
omit [Fintype I] [Fintype J] in
lemma Labor.properT (h:ℕ): Ok (tariff h (smallLength P) s):= l.properO F (by
  filter_upwards [l.large.pos,l.tiny.pos] with a hs hq z he; have hv:=hs z he; have hu:=hq z he; unfold tariff; positivity)

omit l in
lemma properF {d:I→ℕ} : Safe trail (Ready M δ) duo (fun t (z:Scene)=> t/weightCost d e t z) :=
  safe_weight d e (w:=fun s _=>s) (by filter_upwards [self_mem_nhdsWithin] with t (ht:0<t) _ _; exact ht.le)
omit l in
lemma properW (h:ℕ){d:I→ℕ} : Safe trail (Ready M δ) duo
    (fun t (z:Scene)=>(t+(z.logFrom/t)^(h+1))/weightCost d e t z):= safe_weight d e (by
  filter_upwards [self_mem_nhdsWithin] with t (ht:0<t) z hz; have h:=hz.1; positivity)

include Hw Hw' hu hv hG Ht
lemma phases:gapₗ s (fun a z=> whole (Vₗ a z) (xₗ a z) (u₁ a z) (yₗ a z) (wₗ a z)-
    whole S (xₗ a z) (u₁ a z) (yₗ a z) (wₗ a z)):= by
  let μ a z:= traceCharge F d e (s a z) (P a z)-traceCharge F d e (s a z) {(P a z) with viewer:=none}
  have he (d':I→ℕ) (e':J→ℕ) a z (u:Labels S d')(v:Labels S e'):
      (traceCharge F d' e' (s a z) (P a z)-traceCharge F d' e' (s a z) {(P a z) with viewer:=none}) u v=
        whole (Vₗ a z) (xₗ a z) u (yₗ a z) v-whole S (xₗ a z) u (yₗ a z) v:= by
    change trace F _ _ (P a z).viewer u v - trace F _ _ none u v = _; rw [trace_apply,trace_apply]; rfl
  apply (performance (Φ:=μ) F R Jp l.tiny l.large Hw Hw' hu hv (l.properS F) ?budget).congr (fun a z=>he ..)
  intro p q
  let d' := low (d:=d) F R p; let e' := low (d:=e) F R q
  apply (pullLabor l (phase_offer F d' e' hG Ht l.nonneg l.clearance (actors F R p) (actors F R q))
    (properF F)).price
  refine l.common.mono ?_; intro a hr z hz; try dsimp only
  have hx:= (hr z hz).1
  apply le_of_eq; unfold μ; rw [he, he]; apply congrArg norm; apply congrArg₂ (·-·)
  · exact whole_include F (xₗ a z) _ (P a z).viewer (fun i=>Cast.costs F R (p i)) (fun i=>Cast.costs F R (q i))
      (actors F R p) (actors F R q) hx
  exact whole_include F (xₗ a z) _ none (fun i=>Cast.costs F R (p i)) (fun i=>Cast.costs F R (q i))
      (actors F R p) (actors F R q) hx
lemma shadow_norm (h:ℕ):gapₗ (tariff h (smallLength P) s) (fun a z=> discrepancy (Vₗ a z) h (xₗ a z) (oₗ a z) (u₁ a z)
    (shadowOld R.port h (xₗ a z) (oₗ a z) (u₁ a z)) (yₗ a z) (wₗ a z)):=by
  apply (performance (Φ:=fun a z=>shadowCharge F R.port d e h (s a z) (P a z)) F R Jp l.tiny l.large Hw Hw'
      hu hv (l.properT F h) ?budget).congr (fun a z=> shadowError_apply ..)
  intro p q
  apply (pullLabor l (shadow_offer F (low F R p) (low F R q) hG Ht l.nonneg l.clearance h (actors F R p) (actors F R q))
    (properW F h)).price
  refine l.common.mono ?_; intro a hr z hz; apply le_of_eq; obtain ⟨hx,hy⟩:=hr z hz; apply congrArg norm; exact
    shadowError_inclusion F _ _ (oₗ a z) h _ R.port R.spans (fun i=>Cast.costs F R (p i)) (fun i=>Cast.costs F R (q i))
      (actors F R p) (actors F R q) hx hy
end YM.Integration.GradedFar.Fork
