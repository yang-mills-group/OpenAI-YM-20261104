import YM.RG05Readout.Chalice.Gospel
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Chalice
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Petals Petals.Kernel Bay Dash
/-!
 # D64/D02 style integration with joint projected bodies. Subsequence view Tendsto for word kernels with compact weights. No period volume after Root.D. -/
section
local notation "V"=> Fin n
noncomputable def certificate (V': Fin n→Trial C)(q: Test n) (i:ℕ×ℕ) := (C.S.a i.1:ℂ)^(4*n)*∑ x: Fin n→ Site (C.side i.1 i.2),q (Order.cells C i.1 i.2 x)*UVExt.Slots.probes i.1 i.2 n V' x
variable (P Q': Fin n→Trial C)(u:Test n)
-- Adapt D02.answer to arbitrary two campaigns
lemma alive_seam (hn:∀ s:ℝ,0<s →∃ b:Cutoffs→ℝ,(∀ i,0≤ b i)∧ Tendsto b f.fuse (𝓝 0)∧ f.late fun N p=>∀ x:Fin n→Site (C.side N p), (∀ i j,i≠j → s ≤ C.S.a N * separation (x i) (x j)) → ‖UVExt.Slots.probes N p n P x - UVExt.Slots.probes N p n Q' x‖≤b (N,p)): Tendsto (certificate P u - certificate Q' u) f.fuse (𝓝 0):=by
   let K:= tsupport u
   obtain ⟨s,hs,hS⟩:=Gaps.someGrows C.S (u.hasCompactSupport) (show K ⊆ conf _ from u.tsupport_subset)
   obtain ⟨b,hb,hV,hX⟩:= hn s hs; obtain ⟨L,hL,h_T⟩:= Order.testSup u -- L notation no
   obtain ⟨M,hM⟩:= (u.hasCompactSupport.image continuous_norm).bddAbove
   let S':= Metric.closedBall (0:Points n) (M+1); have H:IsCompact S':=isCompact_closedBall ..
   let F₁(T:Fin n→Trial C)(i : Cutoffs) (x:Points n):=Extraction.stair (C.S) (fun r:Var C.S n i.1 i.2=>u (Order.cells C i.1 i.2 r)*UVExt.Slots.probes i.1 i.2 n T r) x; let z(k):= S'.indicator fun _=> L*b k; have hm : ∀ᶠ k in f.fuse,∀ x:Points n, ‖(F₁ P k x-F₁ Q' k x)‖ ≤ z k x:=by
      rw [Order.fused]
      filter_upwards [hX,f.per.cofinal.eventually hS] with p hP hv
      filter_upwards [hP, (C.S.shrinks.comp f.mesh.cofinal|>.const_mul (4*n:ℝ)).eventually (ge_mem_nhds (by simp : (4*n:ℝ)*0<1))] with N ht hh x
      let J':Cutoffs:= (f.mesh N, f.per p); let s' :=C.S.a J'.1
      have hw: 0 ≤ z J' x:= indicator_nonneg (fun _ _=>mul_nonneg hL (hb _)) x
      by_cases he : x∈Fund C.S (f.per p) n
      · let r:= Extraction.bucket (f.mesh N) (f.per p) x (S:=C.S); let q:= Extraction.tag s' (Extraction.address s' x)
        have hc: Order.cells C (f.mesh N) (f.per p) r = q:=by unfold q; rw [show Extraction.address s' x= _ from (show Extraction.address s' x=fun i=> Lattice.lift (r i) from Extraction.found he)];rfl
        change ‖F₁ P J' x-F₁ Q' J' x‖≤_; unfold F₁ Extraction.stair; rw [Set.indicator_of_mem he, Set.indicator_of_mem he]; dsimp only[J']; rw [←mul_sub,hc]; by_cases hu:u q=0; · rw[hu,zero_mul,norm_zero];exact hw
        rw [norm_mul]; have hq:q∈K:= subset_closure hu; have hS': x∈ S':=by
          rw [Metric.mem_closedBall, dist_zero_right]; have Hd : dist x q≤ (1:ℝ):= (dist_comm ..).trans_le ((approximate (C.S.a_pos _) _).trans hh); linarith only [norm_sub_norm_le x q, hM ⟨q,hq,rfl⟩,(dist_eq_norm x q) ▸ Hd]
        have he:=ht r (fun i j hij=> Gaps.gridSeparation C.S r rfl (hv q hq) j i hij.symm)
        unfold z; rw [Set.indicator_of_mem hS']; exact mul_le_mul (h_T _) he (norm_nonneg _) hL
      change ‖F₁ P J' x-F₁ Q' J' x‖≤_; unfold F₁ Extraction.stair; rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he,sub_self,norm_zero];exact hw
   have hx: Tendsto (fun k=> volume.real S'*(L*b k)) f.fuse (𝓝 0):=by simpa only [mul_zero] using ((hV.const_mul L).const_mul (volume.real S'))
   apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ?_ hx; filter_upwards [hm] with k hk
   have he: Integrable (z k):=(integrable_indicator_iff H.measurableSet).mpr (integrableOn_const H.measure_lt_top.ne)
   have ht:= norm_integral_le_of_norm_le he (Eventually.of_forall hk);rw [integral_sub, integral_indicator (f:=fun _=>_) H.measurableSet,setIntegral_const, smul_eq_mul] at ht --
   · change ‖certificate P u k- certificate Q' u k‖≤ _; unfold F₁ at ht; rw [stair_integral,stair_integral] at ht; exact ht
   · exact stair_int _
   · exact stair_int _
include h
variable {p:Fin n→ℕ}{K:YM.Table C.book}
lemma earns {φ:Filter Cutoffs}[φ.NeBot]{s: Caps n} (v:(i:V)→ Rowe C (s i))(t:C.book.Vector s)(hp:f.Ordered C K)(hx:∀ i:Fin n, Reveals C f (P i) (v i))(he:φ≤f.fuse)(hr:CenterPort C f) (hv:∀ i,Tendsto (v i) φ (𝓝 (t i))) : Tendsto (certificate P u) φ (𝓝 (u.applyTo (fun x=>K.value s x t))):=by
   let T:= fun i:Fin n=> Bid.upper C (v i); have ht:= alive_seam P T u fun _ h'=>discrepancy h hr P hx h'
   have he': Tendsto (certificate T u) φ (𝓝 (u.applyTo (fun x=>K.value s x t))):=by
       have heq(i): certificate T u i= Order.smears C i.1 i.2 (fun j:V=>Sigma.mk (s j) (v j i)) u:=by
            unfold certificate Extraction.Order.smears; apply congr_arg; apply Finset.sum_congr rfl; intro k _; rw [Family.num]; apply congr_arg; rfl
       exact (Next.UVStress.calibrated_smear hp φ he u (v:=fun j i=> v i j) hv).congr fun i=> (heq i).symm
   have hh:= (ht.mono_left he).add he'; rw [zero_add] at hh; apply hh.congr; intro i; erw [Pi.sub_apply,sub_add_cancel]
end
end YM.RG05Readout.Chalice
