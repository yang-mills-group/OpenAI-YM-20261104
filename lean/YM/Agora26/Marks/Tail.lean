import YM.Agora26.Marks.Actual
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
namespace Vista26
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
open Vitrines GridApprox
section
variable {a:C.label d}
local notation "F'" => C.labels.level d
local notation "E!" => (Spindle.parcel C d k N p a)
local notation "p0" => (C.path.levels.budget k)
local notation "p!" => (C.path.rep N p k).p
local notation "colX" => (C.path.levels.params k).columns
section
-- reservation tail kept in SAME addressed, masked representation at singleton reference.
-- analytic weight through p.order raw field derivatives on Healthy, supp affine merge
-- as in P.supBounds. Adapted from Vitrines/Left and Maid/tendrils.
variable {a:ℝ}{F:Labels.Frame G d}{X:Rep G n}{Q:Coefficient F n}{o:Site n}(h:Blown Q o X a)
include h
lemma driftReserve (r:ℕ):
    ∃ f:ℕ→ℝ, SumBudget (fun i=>X.p.mass (Q.support i) (if r≤Vitrines.height X Q i then f i else 0)) (Real.exp (-2*(r:ℝ))*a) ∧
    ∀ i,X.p.supBounds o (Q.support i) (Q.regular i) (f i):=by
   obtain ⟨f,hf,hX⟩:=h
   refine ⟨f, Local.sumBudget_mono (Local.sumBudget_mul_left hf (Real.exp_pos _).le) (fun i=> X.p.loMass _ _ (by split; exact (hX i).1; rfl)|>.trans' ?_) (fun i=>?_) le_rfl,hX⟩ -- transpose f nonneg wrong
   · split; exact (hX i).1; rfl
   show _ ≤ Real.exp (-2*(r:ℝ))*reservedMass X.p (Q.support i) (f i)
   split_ifs with ht; swap
   · unfold BudgetPoint.mass; rw [mul_zero]; exact mul_nonneg (Real.exp_pos _).le (hf.1 _)
   unfold BudgetPoint.mass reservedMass; rw [← mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_right (Real.exp_monotone _) (hX i).1
   have he : (r:ℝ) ≤ ↑(coverNumber X.p.B (Q.support i)):= by exact_mod_cast ht
   linarith only [he]
lemma driftCharge (r:ℕ)(U:Config G n): ‖Vitrines.drift X Q r U‖ ≤ Real.exp (-2*(r:ℝ))*a :=by
   obtain ⟨f,hf,hX⟩:= driftReserve h r
   let g i:=X.p.mass (Q.support i) (if r≤Vitrines.height X Q i then f i else 0)
   have hp(i): ‖Vitrines.relict X Q U i r‖ ≤ g i:=by
      unfold g Vitrines.relict; split_ifs with he; swap
      · simp [BudgetPoint.mass]
      refine le_trans ?_ (X.p.loMass _ _ (hX i).1)
      unfold Coefficient.maskedTerm; by_cases hl : Healthy X.p.threshold (Q.support i) U; swap
      · rw [masked_ne _ _ _ _ hl,norm_zero]; exact (hX i).1
      rw [masked_eq _ _ _ _ hl]; exact (hX i).2 U hl [] (by simp) (by simp)
   have hx:= hf.2.1.of_nonneg_of_le (fun i=> norm_nonneg _) hp
   exact (norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum hp hf.2.1).trans hf.2.2)
end
-- Entire regular line's pointwise vs actual localized enamel. NO division by pointwise p
-- (total-part ratio under scene below). Keep forced and masks in proving joint comparison.
abbrev whole (C:Family G)(d k N p:ℕ)(a:C.label d)(o:Site (C.side k p)): Config G (C.side k p)→ℂ:=
   indexX C d N p a (Ribbons.loops C k p o) (1,false) k
local notation "X!" => whole C d k N p a
local notation "Z'" => bead C d k N p
variable (hS:Citizen C W r D) (a:C.label d)(o:Site (C.side k p))(r':ℕ)(hk:k<N)(hr:C.ref d≤k)
local notation "α" => alto C.path k d
include H hS hk hr
lemma crown (U):
   ‖whole C d k N p a o U-bead C d k N p r' a o U‖ ≤ Real.exp (-2*(r':ℝ))* colX * Spindle.paid C d k N p a:= Function.const _ (by
   let F:=F'; let Q:=Spindle.parcel C d k N p a;
   obtain he:= hS.torches d N p k hr hk ((C.factory d N p).terminal.symm a)
   change Blown Q 0 _ (colX*F.coeffSize (F.core Q.x)) at he
   have hp : 1 ≤ colX:= (T|>.params k).columns_ge
   let X:= C.path.rep N p k; let E(v):= Q.exponentialEntry 0 (C.localSection d) X v
   let U':= pull 1 o U
   unfold whole indexX
   rw [Ribbons.same]
   change ‖α*E U' - α*(E U'-Vitrines.drift X Q r' U')‖ ≤ _
   rw [← mul_sub,sub_sub_cancel,norm_mul,mintedLabel (N:=N) (k:=k) (p:=p) a]
   apply (mul_le_mul_of_nonneg_left ((driftCharge he r' U').trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rotate_core F Q.x) (by linarith)) (Real.exp_pos _).le)) (norm_nonneg _)).trans_eq
   ring) H

lemma wholeSize (U): ‖whole C d k N p a o U‖ ≤3*(colX * Spindle.paid C d k N p a):= Function.const _ (
   (scratch C a k p N _ _ H.seed hr hk.le U).1) hS
lemma beadSize (U): ‖bead C d k N p r' a o U‖ ≤ 4*(colX * Spindle.paid C d k N p a):=by
   let q:=colX* Spindle.paid C d k N p a; have hq : 0 ≤ q:= paid_pos C d k N p a|>.trans (le_mul_of_one_le_left (paid_pos ..) ((C.path.levels.params k).columns_ge)) -- name arity
   have ht : Real.exp (-2*(r':ℝ))≤1:= Real.exp_le_one_iff.mpr (by simp)
   have hh:= crown H hS a o r' hk hr U; rw [norm_sub_rev,mul_assoc] at hh
   have hx:= wholeSize H hS a o hk hr U
   have hu : bead C d k N p r' a o U=(bead C d k N p r' a o U-whole C d k N p a o U)+whole C d k N p a o U:= by ring
   calc
    _ ≤ ‖bead C d k N p r' a o U-whole C d k N p a o U‖ + ‖whole C d k N p a o U‖:= (congr_arg norm hu).le.trans (norm_add_le ..)
    _ ≤ Real.exp (-2*(r':ℝ))*q +3*q:= add_le_add hh hx
    _ ≤ _ := by change _ ≤4*q; nlinarith only [ht,hq, mul_le_mul_of_nonneg_right ht hq]
lemma wholeEnv:Envelope (whole C d k N p a o):=by
    let Q:=Spindle.parcel C d k N p a; let X:= C.path.rep N p k
    constructor
    · unfold whole indexX; rw [Ribbons.same]
      have he:= (H.seed.calibrated d N p (hr.trans hk.le)).format k hr hk.le ((C.factory d N p).terminal.symm a)
      change Q.Format 0 C.params X at he
      change Measurable (fun U=>α*Q.exponentialEntry 0 (C.localSection d) X (pull 1 o U))
      apply measurable_const.mul
      refine Measurable.comp (f:=pull (1:Signed) o) (g:= Q.exponentialEntry 0 (C.localSection d) X) ?_ (continuous_pull ..).measurable
      unfold Coefficient.exponentialEntry
      apply Measurable.add _ (Measurable.tsum fun i=>masked_measurable _ _ _ (he.smooth i).borel)
      exact measurable_const.add (masked_measurable _ _ _ ((C.localSection d).continuous_places .. |>.measurable))
    exact ⟨_,wholeSize H hS a o hk hr⟩
end
end Vista26
end YM.OPE.Strobe
namespace YM.OPE.Strobe.Vista26
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge} {C:Family G} {k m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "T" => C.path.levels
open GridApprox
private lemma prod_dist {X:Type} (F E:J→X→ℂ)(U:X){M ε:ℝ}(hs:1≤M)
    (hf:∀ j, ‖F j U‖ ≤ M)(hv:∀ j, ‖E j U‖ ≤M)(he:∀ j, ‖F j U-E j U‖≤ε)(hp:0≤ε)(q:Finset J):
    ‖∏ j∈q,F j U - ∏ j∈q,E j U‖ ≤ q.card*ε*M^q.card:= Function.const _ (by
    induction q using Finset.induction_on with
    | empty=> simp
    | insert i s hi ih=>
      let X:=∏ j∈s,F j U; let Y:=∏ j∈s,E j U; let n:=s.card
      have hy: ‖Y‖ ≤ M^n:=by
         unfold Y; rw [norm_prod]; exact (Finset.prod_le_prod (fun j _=> norm_nonneg _) (fun j _=> hv j)).trans_eq (by simp [n])
      rw [prod_insert hi,prod_insert hi,card_insert_of_notMem hi,pow_succ]; change ‖F i U*X-E i U*Y‖ ≤ _
      rw [show F i U*X-E i U*Y=F i U*(X-Y)+(F i U-E i U)*Y by ring, Nat.cast_add]; refine (norm_add_le ..).trans ?_
      rw [norm_mul,norm_mul]
      refine (add_le_add (mul_le_mul (hf i) ih (norm_nonneg _) (zero_le_one.trans hs)) (mul_le_mul (he i) hy (norm_nonneg _) hp)).trans ?_
      norm_num only [Nat.cast_one]; have hx:ε*M^n≤ ε*M^n*M:= le_mul_of_one_le_right (by positivity) hs
      unfold n at hx; linarith only [hx]) (‹Fintype J›)

local notation "B" => (fun i=>(C.path.levels.budget i).B)
local notation "chi" => C.path.levels.clock.hatBeta
local notation "J!" => J
variable (hS:Citizen C W r D){br:ℕ} (hbr:0<br) (d':J→ℕ)
abbrev regularPack {k N p:ℕ} (x:J→Site (C.side k p)) (v:(j:J)→C.label (d' j)) : J → Config G (C.side k p)→ℂ:=
    fun j=>whole C (d' j) k N p (v j) (x j)
include hS H
private lemma entire {φ:Filter I}{k dis:I→ℕ}(L:GracesP C φ k dis){src tar:I→ℝ}(hv:Coins φ (C.S.scale ∘ k) src)(hvpos:∀ᶠ i in φ,0<src i)
    (hs:Coins φ (C.S.scale ∘ k) tar)(ht:∀ᶠ i in φ,0<tar i):
    ∀ᶠ i in φ, ∀ N p:ℕ,k i<N→ ∀ x:J→Site (C.side (k i) p), ∀ v:(j:J)→ C.label (d' j),
      (∀ j, Spindle.paid C (d' j) (k i) N p (v j) ≤ src i)→ ∀ slots:Finset J,
        ‖(∫ U,fineJob (regularPack (N:=N) d' x v) slots U ∂ (Therm.scene C.path N p (k i))) - (∫ U,fineJob (ScenePack (N:=N) d' x v) slots U ∂ (Therm.scene C.path N p (k i)))‖ ≤ tar i:=by
    let A(i:ℕ):=(T|>.params i).columns; let u:= C.S.scale ∘ k; let c:= fun i=> A (k i) * src i
    have h0 : Tendsto u φ atTop:= C.S.divergent.comp L.seeks
    have hA : Cheap φ u c:= Cheap.mul (show Coins φ u (fun i=> («A» : ℕ → ℝ) (k i)) from columns_p h0 H.cuts.toPackage.toTableTickets L.ages).up hv.up
    let v i:=1+4*c i; have hB:Cheap φ u v:= Bill.add (Bill.const (1:ℝ) h0) (Cheap.mul (Bill.const (4:ℝ) h0) hA) h0
    let n:=Fintype.card J; let q(i):=(n:ℝ)* c i * v i^n
    have hq:Cheap φ u (fun i=>q i/tar i):=Cheap.div (Cheap.mul (Cheap.mul (Bill.const (n:ℝ) h0) hA) (Cheap.power hB h0 n)) hs
    filter_upwards [stainBeat H L hq,hvpos,ht,eventually_all.mpr fun j=>L.seeks.eventually_ge_atTop (C.ref (d' j))] with i h hv ht hr N p hk x s he slots
    let F(j:J):=regularPack (N:=N) d' x s j; let E(j:J):=ScenePack (N:=N) d' x s j
    let M:=v i; let X' j:= Spindle.paid C (d' j) (k i) N p (s j)
    have ha:0≤A (k i):= zero_le_one.trans (C.path.levels.params _).columns_ge
    have hh(j): A (k i) * X' j ≤ c i:= mul_le_mul_of_nonneg_left (he _) ha
    have hv : 0 ≤ c i:=mul_nonneg ha hv.le
    have heM : 1≤M:=by unfold M v; linarith
    let B':= Real.exp (-2*(B (k i):ℝ)); have hμ :0 ≤ B'*c i:= by unfold B'; positivity
    have hY (U): ‖fineJob F slots U-fineJob E slots U‖ ≤ tar i:=by
       have hV:= prod_dist F E U heM (fun j=> ((wholeSize H hS (s j) (x j) hk (hr j) U).trans (mul_le_mul_of_nonneg_left (hh j) (by norm_num))).trans (show 3*c i≤M by unfold M v; linarith)) (fun j=> ((beadSize H hS (s j) (x j) (B (k i)) hk (hr j) U).trans (mul_le_mul_of_nonneg_left (hh j) (by norm_num))).trans (show 4*c i≤M by unfold M v; linarith)) (fun j=>by
          have hX:= crown H hS (s j) (x j) (B (k i)) hk (hr j) U; rw [mul_assoc] at hX; exact hX.trans (mul_le_mul_of_nonneg_left (hh j) (Real.exp_nonneg _))) hμ slots
       have hd : ((slots.card):ℝ) ≤ n:= by unfold n; exact_mod_cast card_le_univ slots
       have hx: q i / tar i * B' ≤ 1:= le_trans (mul_le_mul_of_nonneg_right (Real.le_norm_self _) (Real.exp_nonneg _)) h.2
       rw [div_mul_eq_mul_div, div_le_iff₀ ht, one_mul] at hx; unfold q at hx
       exact hV.trans ((mul_le_mul (mul_le_mul_of_nonneg_right hd hμ) (pow_le_pow_right₀ heM (card_le_univ slots)) (by positivity) (by positivity)).trans (by convert hx using 1; change (n:ℝ)*(B'*c i)*M^n=_; unfold M; ring))
    haveI := Therm.probability H.seed.wilson hk.le (p:=p)
    let mu:=Therm.scene C.path N p (k i)
    have hF : Integrable (fineJob F slots) mu:=(Envelope.prodC _ F (fun j _=>wholeEnv H hS (s j) (x j) hk (hr j))).integrableC _;
    have hE : Integrable (fineJob E slots) mu:=(Envelope.prodC _ E (fun j _=>cylinder_env (Strobe.bead_local H _ (s j) (hr j) hk.le _))).integrableC _
    change ‖(∫ U,fineJob F slots U ∂mu)-(∫ U,fineJob E slots U ∂mu)‖ ≤ _; rw [← integral_sub hF hE]
    exact (norm_integral_le_of_norm_le_const (Eventually.of_forall hY)).trans (by simp) -- check lemma
include hbr
lemma completeIntegral {φ:Filter I}{k dis:I→ℕ}(L:GracesP C φ k dis){src tar:I→ℝ}(hv:Coins φ (C.S.scale ∘ k) src)(hvpos:∀ᶠ i in φ,0<src i)
    (hs:Coins φ (C.S.scale ∘ k) tar)(ht:∀ᶠ i in φ,0<tar i):
    ∀ᶠ i in φ, ∀ N p:ℕ,∀ hk:k i<N,∀ x:J→Site (C.side (k i) p), Sites26 (C:=C) br (dis i) x → ∀ v:(j:J)→ C.label (d' j),
      (∀ j, Spindle.paid C (d' j) (k i) N p (v j) ≤ src i)→ ∀ slots:Finset J,
        ‖moment (C.beta N p) (fineJob (BarePack d' x hk.le v) slots) - (∫ U,fineJob (regularPack (N:=N) d' x v) slots U ∂ (Therm.scene C.path N p (k i)))‖ ≤ tar i:=by
    let q i:=tar i/2; have hq: ∀ᶠ i in φ,0<q i:=ht.mono fun i hi=> div_pos hi zero_lt_two; have he:Coins φ (C.S.scale ∘ k) q:= Coins.div hs (Bi.const 2 (by norm_num) (C.S.divergent.comp L.seeks))
    filter_upwards [productLaw H L hS hbr d' hv hvpos he hq, entire H hS d' L hv hvpos he hq] with i hi ha N p hk x hx v hE slots
    let z(m:J→ Config G (C.side (k i) p) → ℂ):=∫ U,fineJob m slots U∂ Therm.scene C.path N p (k i)
    let a:= moment (C.beta N p) (fineJob (BarePack d' x hk.le v) slots); let b:= z (ScenePack (N:=N) d' x v); let c:=z (regularPack (N:=N) d' x v)
    have hb:‖a-b‖≤q i:= hi N p hk x hx v hE slots
    have hC:‖b-c‖ ≤ q i:= (norm_sub_rev _ _).trans_le (ha N p hk x v hE slots)
    change ‖a-c‖ ≤tar i; refine (norm_sub_le_norm_sub_add_norm_sub a b c).trans ((add_le_add hb hC).trans_eq ?_); unfold q; ring

lemma completeNative (e t s:ℕ):
    ∀ᶠ k:ℕ in atTop, ∀ dis:ℕ,(C.path.levels.budget k).B^8 ≤ dis → (dis:ℝ) ≤ C.path.levels.clock.hatBeta k^e→
    ∀ N p:ℕ,∀ hk:k<N,∀ x:J→Site (C.side k p), Sites26 (C:=C) br dis x → ∀ v:(j:J)→ C.label (d' j),
      (∀ j, Spindle.paid C (d' j) k N p (v j) ≤ C.path.levels.clock.hatBeta k^t)→ ∀ slots:Finset J,
        ‖moment (C.beta N p) (fineJob (BarePack d' x hk.le v) slots) - (∫ U,fineJob (regularPack (N:=N) d' x v) slots U ∂ (Therm.scene C.path N p k))‖ ≤ (C.path.levels.clock.hatBeta k^s)⁻¹:=by
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
   have hx:= completeIntegral H hS hbr d' (show GracesP C M0 K n from ⟨h,(Cheap.power hp.up hz e).norm_le (hB.mono fun i (hi:i∈A)=> (Real.norm_of_nonneg (Nat.cast_nonneg _)).trans_le (hi.2.trans (Real.le_norm_self _))),hB.mono fun i (hi:i∈A)=> hi.1⟩) (hk t) (Eventually.of_forall fun i=> hv (K i) _) (Coins.inv (hk s)) (Eventually.of_forall fun i=> inv_pos.mpr (hv (K i) _)); rw [Filter.eventually_inf_principal] at hx
   obtain ⟨u,hu,hU⟩:= hx; filter_upwards [hu] with i hi b he hx
   exact hU (show (i,b)∈ K ⁻¹' u from hi) ⟨he,hx⟩
end YM.OPE.Strobe.Vista26

