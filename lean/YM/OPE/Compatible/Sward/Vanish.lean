import YM.OPE.Compatible.Sward.Lucent
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
open Matrix
variable {c:Side}
lemma bulL (h:c.val∣N.val)(a:Site N)(p:Seat k m (Shade H))(v:Bid.Dir H c) : LightP a (m:=m) p (Booklet h H v)= LightP (trimT N c h a) (m:=m) p v:= by
          unfold LightP Flair Flume.Script.value scribe; apply Finset.sum_congr rfl; intro i _; refine tsum_congr (fun b=>congr_arg (lilies m k _ p i b*·) ?_); apply Finset.prod_congr rfl; intro j _; change spool H c v (trimT N c h (a+wrap N (b j).1),(b j).2) = _; rw [_root_.map_add,lease]
lemma warmth (x:Site N)(v:Bid.Dir H N):Continuous fun p:Seat k m (Shade H)=>LightP x (m:=m) p v:=by
        let I:= Shade H; let y:= spool H N v; let Y(p:Seat k m I):= worldR m k x I p; simp_rw [LightP,cadillac]; unfold Strike Tensor.diagonal; refine continuous_finsetSum _ ?_; intro i _; convert! (ContinuousMultilinearMap.apply ℝ (fun _ :Fin i=>deck I N) ℝ (fun _=>y)).continuous.comp ((reading m i x).continuous.comp (moduleAt m k i I).continuous) using 1
variable {n₀:ℕ}
lemma lucid (C: KernelChoices)(v:Train r)(h:4 ≤ r) (p: I→Seat k m (Shade H))(q:Seat k m (Shade H))(u:I→Side)(X:I→ℝ)(hp:∀ i,c.val∣ (u i).val) (l:Filter I)[l.NeBot] (ht:Tendsto (fun i=> (u i).val) l atTop)(hg:Tendsto X l (𝓝 D))(hh:Tendsto p l (𝓝 q)) :
       (∀ᶠ i in l, let n:=u i; let mθ:= Chart.tangent H (Exterior.Body 1 n); let A:= Vessel C v H n h; let z:=LightP (0:Site n) (m:=m) (p i)
                    settled (m:=m) (p i) ∧ 0≤X i ∧ ∃ g: Bid.Dir H n →ℝ, Husk mθ A j g ∧ anthem d g ∧ ∀ x:Bid.Dir H n,(n.val:ℝ)^5*‖z x-g x‖ ≤ X i*(1+‖spool H n x‖)^n₀) → LightP (0:Site c) (m:=m) (boostS (atlasF H v h C) (1/2) m k q)∈ Breeze (Bid.Dir H c) j d:=by
          intro hc; let M(i:I):= Chart.tangent H (Exterior.Body 1 (u i)); let P(i):= Vessel C v H (u i) h; let f(i:I):= LightP (0:Site (u i)) (m:=m) (p i); let W:= Shade H
          choose g ha using show ∀ i,∃ g: Bid.Dir H (u i)→ℝ,(Husk (M i) (P i) j g ∧ anthem d g ∧∀ x:Bid.Dir H (u i), ((u i).val:ℝ)^5*‖f i x-g x‖≤X i * (1+‖spool H (u i) x‖)^n₀ ) ↔ ∃ g: Bid.Dir H (u i)→ℝ,Husk (M i) (P i) j g ∧ anthem d g∧∀ x:Bid.Dir H (u i),((u i).val:ℝ)^5*‖f i x-g x‖≤ X i*(1+‖spool H (u i) x‖)^n₀ from fun i=>by
                by_cases ht:∃ g: Bid.Dir H (u i)→ℝ,Husk (M i) (P i) j g ∧ anthem d g∧∀ x:Bid.Dir H (u i),((u i).val:ℝ)^5*‖f i x-g x‖≤ X i*(1+‖spool H (u i) x‖)^n₀
                · obtain ⟨g,hg⟩:= ht; exact ⟨g,fun he=>⟨g,he⟩,fun _=>hg⟩
                exact ⟨0,fun h=>⟨0,h⟩,fun h=>(ht h).elim⟩
          let L(i:I):= Booklet (hp i) H; let B(i:I):=Dawn (M i) (P i) (f i) ∘ (L i).toLinearMap;
          let F(i:I):=Dawn (M i) (P i) (g i) ∘ (L i).toLinearMap; refine sweepC (L:=l) F _ ?_ ?_
          · intro x
            let T:= atlasF H v h C; let q':= boostS T (1/2) m k q; have he: Tendsto (fun i=> B i x) l (𝓝 (LightP (m:=m) 0 q' x)):=by
                         let V(i:I):= boostS (rentV H v h C (u i)) (1/2) m k (p i); have hpV:= (show Tendsto V l (𝓝 q') from fixStrong (loreLap (wave _ ht H v h C)) _ _ hh); apply ((warmth (k:=k) (m:=m) 0 x).continuousAt.tendsto.comp hpV).congr'; filter_upwards [hc] with i hv; change _= Dawn (M i) (P i) (LightP _ (m:=m) _) (Booklet _ _ x); rw [show Dawn _ _ _= _ from wellD (L:=C) _ (m:=m) _ v h hv.1, bulL, _root_.map_zero]; rfl
            let z(i:I):= B i x - F i x; have hV:Tendsto z l (𝓝 0):=by
                 let mZ:= quotaB W ((terra_money C h).choose+1) n₀; have hz:0≤mZ:=by unfold mZ quotaB; have hp:0 ≤ (terra_money C h).choose:=(terra_money C h).choose_spec.1; positivity
                 let X':=spool H c x; let U:= (1+‖X'‖)^n₀; let n(i):ℝ:= (u i).val; apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg (z i)) ?_ (show Tendsto (fun i=>mZ*U*X i/n i) l (𝓝 0) from (hg.const_mul _).div_atTop (tendsto_natCast_atTop_atTop.comp ht))
                 filter_upwards [hc] with i ⟨hv,hy,hG⟩; obtain ⟨hH,hp1,hp'⟩:= (ha i).2 hG; apply (canyon (L i x) _ hy (f i) _ n₀ (show Bond (f i) from (polW (m:=m) _ (p i)).cost) hH.coin hp' C v h).trans; change mZ*_ * X i/n i≤_; refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by gcongr; exact book_eq ..) n₀) hz) hy) (Nat.cast_nonneg _)
            convert (he.sub hV) using 1; ext1 i; unfold z; ring; rw[sub_zero]
          filter_upwards [hc] with i hi; obtain ⟨ht,hq,hh⟩:= (ha i|>.2 hi.2.2); exact Duration (M i) (P i) (L i) (g i) ht hq -- adjust
end YM.OPE.Silt.Phere
