import YM.FormalOPE.RG10.Shutters.Leaning
/-! Coherent if choosing a parity-compatible Official at all heights (as in trace option).
Never assumes all-order "+ sign stress" for coupled arrays away from the hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Shutters
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
  RG10.Position
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d n:ℕ}(q:ℕ+){P:Plan F}
section parity
variable {I Q:Type*}[Fintype I]{shape:Q→ℕ}{w:I→ℕ}{E: TestSystem I Q shape}
local notation "ℳ" => Mark I shape
local notation "Z"=>E.Z
variable {J:Type*} {F':Filter J}
namespace Blinds

-- local uniqueness under parity-conjugating the shift
lemma shade (L:Blinds w E)(A:ℳ→ ℝ) {x:J→ℳ→ℝ}(u:E.Regular A)(hh:∀ v,Tendsto (fun j=> x j v) F' (𝓝 (A v)))
    (η:∀ᶠ i in F', glow shape w (x i)=x i) : ∀ᶠ i in F', Blinds w (E.leadingAdjust A (x i)) := by
  let a:= A ∘ markIn E.tests; let p i:= (x i) ∘ markIn E.tests; let B i:= E.branch A (p i); let t i:= L.mirror (B i)
  have he : Tendsto p F' (𝓝 a):=tendsto_pi_nhds.mpr (fun _=>hh _)
  have hb : Tendsto (fun i=> (p i,B i)) F' (𝓝 (a,0)):= (E.tends A u).comp he
  have hz : Tendsto (fun i=>(p i,t i)) F' (𝓝 (a,0)):= he.prodMk_nhds (show Tendsto t F' _ from (show L.mirror 0=0 from map_zero _) ▸ (L.mirror.continuous_of_finiteDimensional.continuousAt.tendsto.comp hb.snd_nhds))
  let D:=fderiv ℝ E.solver (a,0)
  let Q:=(LinearEquiv.ofBijective D.toLinearMap ((E.eventually_fullrank A u).self_of_nhds)).toContinuousLinearEquiv
  have hv: HasStrictFDerivAt E.solver Q.toContinuousLinearMap (a,0):= E.smooth_solve.hasStrictFDerivAt (by simp)
  have hk:= HasStrictFDerivAt.eventually_left_inverse (f':=Q) hv
  filter_upwards [hb.eventually hk,hz.eventually hk,he.eventually (E.solves A u),η] with i hk hk' hB η'
  have hd : E.solver (p i,t i)= E.solver (p i,B i):= by
    unfold TestSystem.solver; congr 1
    unfold t p; rw [L.constant _ (x i) η']; unfold p B at *; rw [hB]; exact Subtype.ext L.calm
  have hy : t i=B i:= congr_arg Prod.snd (hk'.symm.trans ((congr_arg _ hd).trans hk))
  have hr : glass w (E.baseline + (B i).val)=E.baseline + (B i).val:= glass_add w _ _ |>.trans (congr_arg₂ (·+·) L.baseline (congr_arg Subtype.val hy))
  exact ⟨hr,L.dark,L.even,L.calm⟩
end Blinds
end parity

def Lantern (D:Stock F) := ∀ i, Blinds (Deck.slots F i) (D i)
local notation "a" => PertExtension.Physical.Profile.n
local notation "ℳ" => Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "w"=> Deck.slots F d

variable (h:Lantern P.stock)(H:Official P.stock)(hq:1<q.val)
include h H hq
lemma merit : ∀ᶠ m in atTop, doze w (P.poses q m d)=P.poses q m d := by
 have hE : ∀ᶠ m in atTop, Blinds w (P.beginsAt q m d):= by
   let X (m:ℕ) (v:ℳ):= constantCoeff (P.begins q m d v)
   apply Blinds.shade (h d) (Physical.free (L:=Maxwell.standard F) (deck F d)) (x:=X) (H.fresh d) (fun i=> Plan.starts hq P i);
   filter_upwards with j; let b:= P.begins q j d; have hh: constantCoeff ∘ b= glow a w (constantCoeff ∘ b):= by
     have hh:= glance a w b 0; rw [begins_snooze] at hh; simp [lapse,comp_def] at *; exact hh
   exact hh.symm
 filter_upwards [hE,Plan.complete hq H d] with m he ht; exact he.stack_kind _ (begins_snooze ..) ht
lemma dresses : ∀ᶠ m in atTop, snooze a w (P.dressed q m d) = P.dressed q m d := by
 filter_upwards [merit (d:=d) q h H hq] with m hm; unfold Plan.dressed; rw [← gaze_transition,begins_snooze,hm]
end YM.FormalOPE.RG10.Shutters
