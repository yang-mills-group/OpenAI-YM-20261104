import YM.X.Scheme.Measure
/-!
Tail coherence all *coupling* coefficients at once at the finite regulator; filtration/involution. No regulator convergence p>0 or coupling here. Use for later all-order part. Naming K.Shop. Detector closure.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bare.Shop
open Function Filter Set Pert Pert.Position Detector Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F:Labels.Frames G} (K:Shop F) (h:G.Simple) (q:ℕ+)(hq:1<q.val)
variable {d e k : ℕ} (p:d≤e)
local notation "H" => nested F h K
local notation "L"=>zoomL F p
local notation "Y"=>Buffer F d

def ftReport (k d:ℕ) : ℕ→Buffer F d:= (nested F h K d).report (K.bank q k d)
def uncut (k d:ℕ):ℕ→Bank F d:= predMarket (K.ftReport h q k d) (K.bank q k d)
include hq
lemma report_sticks (d:ℕ): Tendsto (fun k=>K.ftReport h q k d 0) atTop (𝓝 0):= by
   simp_rw [ftReport,report_zero]; exact (H d).appears_solve0 (q:=fun k=>K.bank q k d 0) (fun i=> K.bank_white q hq i)
lemma chamber (d:ℕ): ∀ᶠ k:ℕ in atTop,(H d).announce (K.bank q k d) (K.ftReport h q k d)∧IsUnit (motor F (K.ftReport h q k d 0)):=
  (((H d).patches (q:=fun k=>K.bank q k d 0) (fun i=>K.bank_white q hq i)).mono fun k hv=> (H d).patch_announces (w:=K.bank q k d) hv).and ((report_sticks K h q hq d).eventually (invertible_tail F d))
lemma report_up : ∀ᶠ k in atTop,L ∘ (K.ftReport h q k e)=K.ftReport h q k d:= by
   let W:= K.ftReport h q; let B:=K.bank q; let D:=H d; let E':= H e; let U:=pulls (up F p)
   have H1 k : B k d=U ∘ B k e:= funext (fun i=>(bank_zoom K q k p i).symm)
   let g(k):= W k d; let f(k):= W k e
   have he : Tendsto (fun k => L (f k 0)) atTop (𝓝 0):= by
      rw [← map_zero L]; apply (show Continuous L from (by exact (LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=Buffer F e) (F':=Buffer F d) L).continuous)).continuousAt.tendsto.comp (report_sticks K h q hq e)
   filter_upwards [(K.chamber h q hq e), D.legal (q:=fun k=>K.bank q k d 0) (fun s=> K.bank_white q hq s) he,D.patches (q:=fun k=> K.bank q k d 0) (fun s=>K.bank_white q hq s)] with k hk hka ha
   suffices ht: D.announce (B k d) (L ∘ f k) by
      refine D.patch_only (w:=K.bank q k d) ha ?_ ht; apply Eq.symm (hka.mp ?_); have he:= congr_fun (show _=_ from ht) 0; rw [Function.comp_apply,pred_zero] at he; exact he
   unfold announce; rw [H1]; have h₁:=congr_arg (fun t=>L ∘ t) (show E'.D ∘ predMarket (f k) (B k e)=_ from hk.1)
   rw [show predMarket (L ∘ f k) (U ∘ B k e)=_ from pred_pulls p]; funext i
   calc
   _ = L ((E'.D ∘ predMarket (f k) (B k e)) i):=(zoom_compat F h K p _).symm
   _ = L (just (E'.D (pureBank F e)) i):= congr_fun h₁ i
   _ = _ := by unfold just; split_ifs; exact (zoom_compat F h K p _).trans (by rw [pure_zoom]); exact map_zero _
lemma uncut_up : ∀ᶠ k in atTop, pulls (up F p) ∘ (K.uncut h q k e)=K.uncut h q k d:=by
    filter_upwards [report_up K h q hq p] with k hk; unfold uncut; rw [← hk,show K.bank q k d=pulls (up F p) ∘ K.bank q k e from funext (fun i=>(bank_zoom ..).symm),pred_pulls]
omit hq in
lemma bank_signs (q:ℕ+)(k d) : (turn (K.bank q k d))=pulls (par F d) ∘ K.bank q k d:= funext (fun j=>(K.bank_parity q k d j).symm)
-- omit hq
lemma report_par (d:ℕ): ∀ᶠ k in atTop,cPar F ∘ (K.ftReport h q k d)=turn (K.ftReport h q k d):= by
   let L':=cPar F (d:=d); let W (k):= K.ftReport h q k d; let T (k):= K.bank q k d; let P:= pureBank F d
   let D:=nested F h K d
   have hh : Tendsto (fun k=> L' (W k 0)) atTop (𝓝 0):= by
      rw [←map_zero L']; apply (show Continuous L' from (by exact (LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=Buffer F d) (F':=Buffer F d) L').continuous)).continuousAt.tendsto.comp (report_sticks K h q hq d)
   filter_upwards [D.patches (q:=fun k=> T k 0) (fun i=> K.bank_white q hq i), K.chamber h q hq d, D.legal (q:=fun k=> T k 0) (fun i=> K.bank_white q hq i) hh] with k hk hv hW
   let w:= turn (L' ∘ W k); have hz: w 0=L' (W k 0):= turn_zero ..
   have hb:T k=pulls (par F d) ∘ Jet.turn (T k):=funext fun i=>Eq.symm (by rw [show Jet.turn (T k)=_ from bank_signs K q k d]; exact pulls_p ..) -- param scope h
   suffices he: w=W k by
       funext i; have hg : ((-1:ℝ)^i • L' (W k i))=W k i:=congr_fun he i; change L' (W k i)= _; change L' (W k i)=(-1:ℝ)^i • W k i
       nth_rw 2 [← hg]; rw [smul_smul,←mul_pow,neg_one_mul,neg_neg,one_pow,one_smul]
   have HA : D.announce (T k) w:= by
       let M:= pulls (par F d); let b:= W k
       have hx : predMarket w (T k)= turn (M ∘ predMarket b (T k)):= by
          let t:=T k; have hz: turn (M ∘ t)= t:= (show turn (M ∘ t)=M ∘ turn t from funext fun i=>(map_smul M _ _).symm).trans hb.symm
          change predMarket w t= turn (M ∘ predMarket b t)
          conv_lhs=> rw [←hz] -- maybe t defeq
          unfold w L' M b; rw [pred_turn,pred_par]
       unfold announce; rw [hx]; funext i
       have ht:=congr_fun (show D.D ∘ predMarket b (T k)=just _ from hv.1) i
       have hp : M P=P:= all_par K
       change D.D ((-1:ℝ)^i • M (predMarket b (T k) i)) = _; rw [map_smul]; change ((-1:ℝ)^i • D.D ((pulls (par F d)) _))= _; rw [D.color]; rw [Function.comp_apply] at ht; rw [ht]; unfold just; split_ifs with h1
       · subst i; change (-1:ℝ)^0 • cPar F (D.D P)=_; rw [pow_zero,one_smul, ←D.color];rw [show pulls (par F d) P=P from hp]
       · rw [map_zero,smul_zero]
   apply D.patch_only (w:=T k) hk _ HA
   rw [hz]; apply Eq.symm (hW.mp ?_); have hf:= congr_fun (show _=_ from HA) 0; rw [Function.comp_apply,pred_zero,hz] at hf; exact hf
lemma uncut_par (d:ℕ): ∀ᶠ k in atTop,pulls (par F d) ∘ K.uncut h q k d = turn (K.uncut h q k d) := by
   filter_upwards [report_par K h q hq d] with k hk; unfold uncut; rw [← pred_par,hk, ← bank_signs,pred_turn]
end YM.PositionX.Bare.Shop
