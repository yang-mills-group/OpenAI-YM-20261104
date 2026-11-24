import YM.Agora26.Marks.Shell
import YM.Agora26.Marks.Poly
/-!
# General mesoscopic full-law comparison. Integrals of actual nonlinear fields, on
the whole measure. Relative to local masked regular stencil (proxy for singleton);
not Gaussian dominance, full-density variation distance or PT identification.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
namespace Vista26
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
local notation "B" => ((fun i=>(C.path.levels.budget i).B))
open GridApprox
variable {br:ℕ} {φ:Filter I} {k dis:I→ℕ} (L:GracesP C φ k dis)
variable (hS:Citizen C W r D) (hbr:0<br) (d':J→ℕ) {src tar:I→ℝ}
include L hS hbr H

abbrev ScenePack {k N p:ℕ} (x:J→Site (C.side k p)) (v:(j:J)→C.label (d' j)) : J → Config G (C.side k p) → ℂ :=
    fun j=> bead C (d' j) k N p (B k) (v j) (x j)

abbrev BarePack {k N p:ℕ} (x:J→Site (C.side k p))(hk:k≤N) (v:(j:J)→C.label (d' j)) : J → Config G (C.side N p) → ℂ :=
    fun j=> abrade C (v j) N k p (x j) hk

set_option maxHeartbeats 200000 in
lemma paymentsLaw (hv:Coins φ (C.S.scale ∘ k) src)(hvpos:∀ᶠ i in φ,0<src i)
    (hs:Coins φ (C.S.scale ∘ k) tar)(ht:∀ᶠ i in φ,0<tar i):
    ∀ᶠ i in φ, ∀ N p:ℕ,∀ hk:k i<N,∀ x:J→Site (C.side (k i) p), Sites26 (C:=C) br (dis i) x → ∀ v:(j:J)→ C.label (d' j),
      (∀ j, Spindle.paid C (d' j) (k i) N p (v j) ≤ src i)→ ∀ slots:Finset J,
        ‖moment (C.beta N p) (fineJob (BarePack d' x hk.le v) slots) - (∫ U,fineJob (ScenePack (N:=N) d' x v) slots U ∂ (Therm.scene C.path N p (k i)))‖ ≤
        slots.card*tar i*(2+src i)^slots.card :=by
   obtain hEmpty|hN:= isEmpty_or_nonempty J
   · apply Eventually.of_forall; intro i N p hk x hx v he slots; rw [show slots=∅ from by ext x;exact isEmptyElim x]
     haveI := Therm.probability H.seed.wilson hk.le (p:=p)
     simp [fineJob, moment]
   letI : Nonempty J:=hN
   have he(q:Finset J):= shellLaw (J:=(↑q:Type)) H L hS hbr (fun j=> d' j.1) hv hvpos hs ht
   obtain ⟨z,hz,hM⟩:= ((eventually_gt_atTop (C.ref 0)).and (rolls H 0 (Fintype.card J))).exists
   filter_upwards [ht,hvpos,L.pace,eventually_all.mpr he,eventually_all.mpr (fun j=>bolted H L hS (d' j) 1 hM hz)] with i ht hvpos hdis hE hP N p hk x hx v hV slots
   let n':Side:=C.side N p; let m':Side:=C.side (k i) p; let β:=C.beta N p; let mu:= Wilson.law G n' β; let X':=BarePack d' x hk.le v; let Y':= ScenePack (N:=N) d' x v
   let Zz(j:J):= GridApprox.backTo C.path N p hk.le (Y' j); let c'(j:J):= cameo C (d' j) (k i) N p (v j)
   let Wt(t:J→Bool)(j:J):Config G n'→ℂ:= writeF C (v j) N (k i) p (B (k i)) (x j) hk.le (t j)
   have hw (q:Finset J)(t:J→Bool)(ha:∃ j∈q,t j=true): ‖∫ Q,Moment.pick (Wt t) q Q ∂mu‖ ≤ tar i:=by
      let I':Type:=↑q; let x'(j:I'):=x j.1
      have hs: Sites26 (C:=C) br (dis i) x':=⟨fun a b=> hx.close ..,fun a b h=>hx.apart _ _ (fun he=>h (Subtype.ext he))⟩
      have hh':∃ a:I', t a.1=true:=by obtain ⟨a,h,h'⟩:= ha; exact ⟨⟨a,h⟩,h'⟩
      have hi:= hE q N p hk x' hs (fun j=> v j.1) (fun j=> hV _) (fun a=> t a.1) hh'
      have hb: Moment.pick (Wt t) q=fineJob (fun j:I'=>Wt t j.val) univ:=by funext X; exact Finset.prod_subtype q (fun _=>Iff.rfl) _
      rw [hb]; exact hi
   obtain ⟨j,hj,h⟩:= Finset.exists_max_image univ (fun j:J=> omen C (d' j) (k i) (B (k i))) univ_nonempty
   let u:=omen C (d' j) (k i) (B (k i)); have hy(l:J) : Interior (GridApprox.window (x l) u) (Y' l):= (bead_local H _ _ (hP l).rank hk.le (B (k i)) (N:=N) (p:=p)).enlarges (by
      intro v hv; exact sparrow.mpr ((sparrow.mp hv).trans (h _ (mem_univ _))))
   have hY(l):Envelope (Y' l):= cylinder_env (hy l)
   have hZ(l):Envelope (Zz l):= backTo_env C.path N p hk.le (hY l)
   have hB(l): Envelope (X' l):= Envelope.compactC (C.continuousO ..)
   have htZ (t:J→Bool): (fun i=>Moment.write X' Zz c' i (t i))= Wt t:=by
      funext j; exact (erased (k:=k i) (v j) (B (k i)) (x j) hk.le (t j)).symm
   have hσ:= Moment.replacement mu X' Zz c' hB hZ hvpos.le (fun l=>Strobe.cameo_price (v l) (hV l)) ht.le (fun q t h=> htZ t|>.symm ▸ hw q t h) slots
   let g:=fineJob Y' slots; have heq : GridApprox.backTo C.path N p hk.le g=fineJob Zz slots := backs_many C.path u N p (k i) N x slots hy (fun a b he=> (hP j).gain.trans_le (hdis.trans (hx.apart a b he))) hk.le
   have hu: Envelope g:= Envelope.prodC slots _ (fun i _=> hY i)
   have hm': (∫ X,Moment.pick Zz slots X ∂mu)=∫ X,g X ∂(Therm.scene C.path N p (k i)):=by
      change moment β (fineJob Zz slots)=_; rw [← heq]; exact (Therm.onstage H.seed.wilson _ ((GridApprox.backTo_env _ _ _ _ hu).integrableC _)).symm.trans (Therm.retro H.seed.wilson hk.le le_rfl g hu)
   rw [hm'] at hσ; exact hσ

-- Increasing finite precision absorbs the whole horizon & moment price.
-- Do NOT use if the src growth is only RateLE 0 (may exceed any polynomial).
lemma productLaw (hv:Coins φ (C.S.scale ∘ k) src)(hvpos:∀ᶠ i in φ,0<src i)
    (hs:Coins φ (C.S.scale ∘ k) tar)(ht:∀ᶠ i in φ,0<tar i):
    ∀ᶠ i in φ, ∀ N p:ℕ,∀ hk:k i<N,∀ x:J→Site (C.side (k i) p), Sites26 (C:=C) br (dis i) x → ∀ v:(j:J)→ C.label (d' j),
      (∀ j, Spindle.paid C (d' j) (k i) N p (v j) ≤ src i)→ ∀ slots:Finset J,
        ‖moment (C.beta N p) (fineJob (BarePack d' x hk.le v) slots) - (∫ U,fineJob (ScenePack (N:=N) d' x v) slots U ∂ (Therm.scene C.path N p (k i)))‖ ≤ tar i:=by
    let a:= C.S.scale ∘ k
    have hz:Tendsto a φ atTop:= C.S.divergent.comp L.seeks
    let M(i):=2+src i
    have he: Coins φ a M:= Coins.by_le (show Cheap φ a M from Bill.add (Bill.const 2 hz) hv.up hz)
      (hvpos.mono fun i hi=> (show 1 ≤ M i by unfold M; linarith) |>.trans (Real.le_norm_self _))
    let F:=Fintype.card J; let n:ℝ:=F
    let t(i):=tar i/((n+1)*M i^F)
    have hf:0 ≤ n:=Nat.cast_nonneg _
    have hc : Coins φ a t:= Coins.div hs (Coins.mul (Bi.const (n+1) (by linarith) hz) (Coins.power he hz _))
    have hM : ∀ᶠ i in φ,1 ≤ M i:= hvpos.mono (fun i hi=>by unfold M;linarith)
    have hF:∀ᶠ i in φ,0<t i:= (ht.and hM).mono (fun i hi=> div_pos hi.1 (by have hh:=hi.2;positivity))
    filter_upwards [paymentsLaw H L hS hbr d' hv hvpos hc hF,hM,hF] with i hi hM hF N p hk x hx v hV slots
    have hB: ↑slots.card*t i ≤ (n+1)*t i:= mul_le_mul_of_nonneg_right ((by unfold n F; exact_mod_cast card_le_univ slots: (slots.card:ℝ)≤n).trans (le_add_of_nonneg_right zero_le_one)) hF.le
    refine (hi _ _ hk _ hx _ hV _).trans ((mul_le_mul hB (pow_le_pow_right₀ hM (card_le_univ slots)) (by change 0 ≤ M i ^ _; positivity) (by positivity)).trans_eq ?_)
    unfold t; field_simp [show n+1≠0 by positivity, show M i≠0 by linarith]
    rfl

omit L in
/-- Uniform native full-Wilson-law comparison for bounded shape packets; all sufficiently
fine k, all periods and higher cutoffs; any fixed requested hatBeta power after any fixed
polynomial paid price. Smooth-jet/positioning/matching to diagrams *not* asserted. -/
lemma nativeScene (e t s:ℕ):
    ∀ᶠ k:ℕ in atTop, ∀ dis:ℕ,(C.path.levels.budget k).B^8 ≤ dis → (dis:ℝ) ≤ C.path.levels.clock.hatBeta k^e→
    ∀ N p:ℕ,∀ hk:k<N,∀ x:J→Site (C.side k p), Sites26 (C:=C) br dis x → ∀ v:(j:J)→ C.label (d' j),
      (∀ j, Spindle.paid C (d' j) k N p (v j) ≤ C.path.levels.clock.hatBeta k^t)→ ∀ slots:Finset J,
        ‖moment (C.beta N p) (fineJob (BarePack d' x hk.le v) slots) - (∫ U,fineJob (ScenePack (N:=N) d' x v) slots U ∂ (Therm.scene C.path N p k))‖ ≤ (C.path.levels.clock.hatBeta k^s)⁻¹:=by
   let K:ℕ×ℕ→ℕ:= Prod.fst; let n:ℕ×ℕ→ℕ:= Prod.snd
   let a:= C.path.levels.clock.hatBeta; let M:=(Filter.comap K atTop)
   let A : Set (ℕ×ℕ):={q | B (K q)^8≤ n q ∧ (n q:ℝ)≤ a (K q)^e}; let M0:= M ⊓ Filter.principal A
   have h:Tendsto K M0 atTop:= tendsto_iff_comap.mpr inf_le_left
   have hB:∀ᶠ i in M0,i∈A:= (Filter.Eventually.filter_mono (show M0 ≤ Filter.principal A from inf_le_right) ((eventually_principal).mpr (fun _ h=>h)))
   have hw:Height C.S M0 (C.S.scale ∘ K) K 1:= ⟨h,tendsto_const_nhds.congr' (((C.S.divergent.comp h).eventually_gt_atTop 0).mono fun i hi=>(div_self («a»:=C.S.scale (K i)) (ne_of_gt hi)).symm)⟩
   have hz:= C.S.divergent.comp h
   have hp:= hat_price hz hw
   have hk (t:ℕ):Coins M0 (C.S.scale ∘ K) (fun i=>a (K i)^t):= Coins.power hp hz _
   have hv(i)(t:ℕ):0<a i^t:=pow_pos (zero_lt_one.trans ((T).fits.delayed _)) _
   have hx:= productLaw H (show GracesP C M0 K n from ⟨h,(Cheap.power hp.up hz e).norm_le (hB.mono fun i (hi:i∈A)=> (Real.norm_of_nonneg (Nat.cast_nonneg _)).trans_le (hi.2.trans (Real.le_norm_self _))),hB.mono fun i (hi:i∈A)=> hi.1⟩) hS hbr d' (hk t) (Eventually.of_forall fun i=> hv (K i) _) (Coins.inv (hk s)) (Eventually.of_forall fun i=> inv_pos.mpr (hv (K i) _)); rw [Filter.eventually_inf_principal] at hx
   obtain ⟨u,hu,hU⟩:= hx; filter_upwards [hu] with i hi b he hx
   exact hU (show (i,b)∈ K ⁻¹' u from hi) ⟨he,hx⟩
end Vista26
end YM.OPE.Strobe

