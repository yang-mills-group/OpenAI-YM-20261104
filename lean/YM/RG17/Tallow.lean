import YM.RG17.Halites
import YM.MergeProof.Maid
/-! Retain branch all grade
 Entries all masked before specialization. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent Relay MergeProof.Float PhysicalNext.Repeat Lotus GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N p k m d:ℕ)(H:C.Makes)
variable {W:Worth}{w ψ ζ:ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ρ"=> liftVac C.path N p
local notation "α"=> fun i:ℕ=> pinHat C d i
private lemma parrots {x y:ℕ}(h:x ≤ y)(f g:Config G (C.side y p)→ℂ)(hf:Integrable f (prior G _))(hg: Integrable g (prior G _)) : pushTo C.path N p h (f+g)=pushTo C.path N p h f+pushTo C.path N p h g:= by
    induction y,h using Nat.le_induction with
    | base=> simp
    | succ i hi ih=> rw [pushTo_next ..,pushTo_next ..,pushTo_next ..,StepData.push_add ((T).levels.transition_mass ..) _ _ hf hg]; exact ih _ _ (StepData.push_integrable ((T).levels.transition_mass ..) _ hf) (StepData.push_integrable ((T).levels.transition_mass ..) _ hg)
private lemma vignette (j:ℕ): pinHat C d j * ((C.S.block j).val:ℂ)^d=pinHat C d (j+1):= by unfold pinHat; rw [C.S.a_step]; simp only [Complex.ofReal_div,Complex.ofReal_natCast, div_pow,inv_div]; rw [div_eq_mul_inv,mul_comm]
section
variable (X:Extra.Histories.Music (C.labels.level d) C.path N p) {Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{φ:ℕ→ℝ} {hk:k ≤ N} (h:Club C.path C.params (C.localSection d) ζ ψ m k N p w D Z φ hk) (hX:Sung (C.localSection d) C.path N p C.params W (C.ref d) X)
    {j:ℕ} (hx:m ≤ j)
include h hx H
lemma torchLine (hy:j ≤ k): α j • (Z j).density 0 Y! (R j)=pushTo T N p hy (pinHat C d k • (Z k|>.density 0 Y! (R k))):=by
   induction hy using Nat.decreasingInduction with
   | self=> rw [pushTo_self]
   | of_succ i hi ih=>
      have hp:=hx.trans (Nat.le_succ i); have hv:=h.ticks (i+1) hp hi; have ht:= play_integrable T N H.wilson (B:=C.localSection d) ((show i+1 ≤ k from hi).trans hk) hv.1 hv.2 -- specify
      rw [← pastPass T N p (Nat.le_succ i) hi,pushTo_next T N p (le_refl i),pushTo_self,← ih hp,StepData.push_smul _ _ _ _ (show Integrable _ _ from ht),(h.votes i hx hi).1,blast, smul_smul]
      rw [show pinHat C d i * ((C.S.block i).val:ℂ)^d=_ from vignette C d i]
omit h hx
lemma seedLine (b:C.label d) (hy:ℓ ≤ j) (hV:j ≤ N): α j • (parcel C d j N p b).density 0 Y! (R j) = pushTo T N p hV (fun u=> liftVac T N p N u * C.O N p b 0 u):=by
   have hr:= H.calibrated d N p (hy.trans hV)
   induction hV using Nat.decreasingInduction with
   | self=> rw [pushTo_self]; funext u; rw [Pi.smul_apply, smul_eq_mul,parcel,hr.encode]; unfold pinHat; rw [← mul_assoc,← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')), one_mul]; rfl
   | of_succ i hi ih=>
      let Q:=parcel C d (i+1) N p b
      have hh: Integrable (Q.density 0 Y! (R (i+1))) (prior G _):= TransferData.density_int H.wilson hr _ _ (hy.trans (Nat.le_succ _)) hi
      rw [← pastPass T N p (Nat.le_succ i) hi,pushTo_next T N p (le_refl i),pushTo_self, ← ih (hy.trans (Nat.le_succ _)), StepData.push_smul _ _ _ _ hh,parcel, hr.unnormalized _ hy hi, smul_smul, show pinHat C d i * ((C.S.block i).val:ℂ)^d=_ from vignette C d i]; rfl
end
section
variable {φ:ℝ}{Q:Coefficient (C.labels.level d) (C.side k p)}
section
variable (J:ℕ){hk:k ≤ N}(hJ:J ≤ k)
local notation "o"=> fun i=> Mix.camp C p J i
local notation "V"=> Site (C.side J p)
local notation "Bt"=> Stock.census V
local notation "u'"=> hands C p J
local notation "U'"=> center C.S p (hJ.trans hk) 0
variable (f:Config G (C.side N p)→ℂ)
local notation "M'"=> birth (Bt) (R N) (fun i=> (U').copy i f) -- bind hk
include H
lemma gradeIn {w: Site (C.side J p)→ℝ}{a e:ℝ} (hr:Q.Format 0 C.params (R k))(hc: Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) φ) (hf:Continuous f) (hZ:Served (R k) (fun i=> radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k d)) (gust T N p N (M') k hk) (o k) w a e) : pushTo T N p hk (fun U=> ρ N U*f U) = pinHat C d k • Q.density 0 Y! (R k):=by
    let Θ:=gust T N p N (M') k hk
    have ht : (fun U=> ((M') U).part ((Bt).fire 0))=(fun U=> ρ N U*f U):= funext fun U=> by
       rw [boot]; change _* (U').copy 0 f U=_; rw [show (U').copy 0 f=f from Ribbons.cappid C J p N (hJ.trans hk) (fun _=> f) true]; rfl
    have hh : Integrable (M') (prior G _):= (hatCont C N p (fun i=> (U').copy i f) (fun i=> Ribbons.cappedC C J p N (hJ.trans hk) (fun _=> f) (i,true) hf) (by rw [(H.wilson.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    choose K hF hK hh' using fun i:Site (C.side J p)=>sparkling T _ Y! Q (u' i) (o k i) (alto T k d) H.wilson 0 hk (H.sections _) hr hc
    rw [show (fun i => sunny _ _ _ _ _)=fun i=>profile (R k).activities (K i) from funext hF] at hZ
    rw [← ht,← gust_choose T N p (M') hh hk]; funext U; rw [(hZ.relay hK (H.wilson.represents N p k hk).good.labels U).1 (0:V),hh', radiant,handmove C k p J hJ]; exact congr_arg (pinHat C d k * ·) (congr_fun (Ribbons.cappid C J p k hJ (fun _=>_) true) U)
end
variable (X:Extra.Histories.Music (C.labels.level d) C.path N p) {Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{γ:ℕ→ℝ} {hk:k ≤ N} (h:Club C.path C.params (C.localSection d) ζ ψ m k N p w D Z γ hk) (hX:Sung (C.localSection d) C.path N p C.params W (C.ref d) X)
    (b:(C.labels.level d).Coeff) (f:Config G (C.side N p)→ℂ)
local notation "l'"=> (X.tone k|>.plays (-b))
local notation "B"=> (s!).terminal b
include H h hX
lemma spires (hy: (s!).entries=(X.draft C.path).inits) (hn:C.ref d ≤ m) (hr:Q.Format 0 C.params (R k))(hc: Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) φ) (ht:(Z k).exponentialEntry 0 Y! (R k)= Q.exponentialEntry 0 Y! (R k)+(l').exponentialEntry 0 Y! (R k))(hK:profile (R k).activities (Z k).forced=profile (R k).activities Q.forced + profile (R k).activities (l').forced) (he:pushTo T N p hk (fun U=>ρ N U*f U)= pinHat C d k • Q.density 0 Y! (R k)) (j:ℕ) (hm:m ≤ j)(hj:j ≤ k) : pinHat C d j • (Z j).density 0 Y! (R j)= pushTo T N p (hj.trans hk) (fun U=> ρ N U*f U)+ pinHat C d j • (parcel C d j N p (-B)).density 0 Y! (R j) := by
   have hl:=hm.trans hj; have ha:=hn.trans hl
   have hZy :l'=parcel C d k N p (-B):=by unfold parcel; rw [hy,map_neg,LinearEquiv.symm_apply_apply ..]; rfl
   have hp:=(hX.earned k ha hk).earns (-b); have hL:=(H.wilson.represents N p k hk).good
   have hF:(Z k).density 0 Y! (R k)= Q.density 0 Y! (R k)+(l').density 0 Y! (R k):=by
        rw [← Relay.plus hL hc hp.2,← coin_primary,← coin_primary]; rw [ht,← duo_exp Y! hc hp.2]; exact coin_port _ _ (rem_dominated ((h.ticks k hl le_rfl).2)) (rem_dominated ((presentation hr hc hp.1 hp.2).2)) (hK.trans (duo_profile hc hp.2).symm) hL.labels
   rw [torchLine C N p k m d H h hm hj,hF,smul_add,parrots C N p hj _ _ ((play_integrable T N H.wilson hk hr hc).smul _) ((play_integrable T N H.wilson hk hp.1 hp.2).smul _),← he,pastPass T N p hj hk,hZy,seedLine C N p d H _ ha hk,seedLine C N p d H _ (hn.trans hm),pastPass]
end
section
open ComplexConjugate
variable (P:Coefficient (C.labels.level d) (C.side k p)) (U:Config G (C.side k p))
private lemma allzeroes (hz:flags (R k).p.threshold U=∅) : 0 < (R k).eval U ∧ P.density 0 Y! (R k) U = liftVac T N p k U* P.exponentialEntry 0 Y! (R k) U:=by
  refine ⟨?_,?_⟩
  · unfold Rep.eval; rw [Activities.gas_one _ _ hz, mul_one]; exact Real.exp_pos _
  have hg (p' : Finset ℕ) : P.marked (R k) p' U=0 := by
    unfold Coefficient.marked; split; swap; · rfl
    rename_i h
    obtain hv|⟨i,hi⟩:=p'.eq_empty_or_nonempty
    · subst p'; exact Finset.sum_empty
    have hx : (((R k).activities.forced i).inventory)⊆ Finset.biUnion p' (fun i=> ((R k).activities.forced i).inventory) := Finset.subset_biUnion_of_mem (fun i => ((R k).activities.forced i).inventory) hi
    rw [h.2, hz] at hx; exact False.elim (((R k).activities.forced i).inventory_ne.ne_empty (Finset.subset_empty.mp hx))
  unfold Coefficient.density; simp_rw [hg]; simp [liftVac]
include H
lemma spiresUp (v:C.label d) (f:Config G (C.side k p)→ℂ) (ht:ℓ ≤ k) (hx:k ≤ N)(hk:pinHat C d k • P.density 0 Y! (R k)= f+pinHat C d k • (parcel C d k N p (-v)).density 0 Y! (R k)) (h:flags (R k).p.threshold U=∅) {e r:ℝ}(hv:P.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) e)(he:e+(F).coeffSize P.x ≤ r): ‖f U / liftVac T N p k U - Spindle.awakeFull C k N p v U‖ ≤ (1+(C.path.levels.params k).columns)* r / C.S.a k^d := by
   let L v':= Spindle.awakeFull C k N p (d:=d) v' U
   have hz:= (Spindle.on_branch H ht hx p U h); have hS:L 0=0:=by have hQ : L (0+(1:ℂ) • 0)= L 0+1*L 0:=(hz 0).2.2 0 1; simpa only [one_smul,add_zero,one_mul,left_eq_add] using hQ
   have hA:L (-v)= -L v:= by have hQ:L (0+(-1:ℂ) • v)=L 0+(-1)*L v:=(hz 0).2.2 v (-1); simpa only [neg_one_smul,neg_mul,zero_add,hS,one_mul] using hQ
   let V:=liftVac T N p k U; let Q:= pinHat C d k; let a:=P.exponentialEntry 0 Y! (R k) U; have hV:=allzeroes C N p k d P U h; have hV': V≠0:=Complex.ofReal_ne_zero.mpr hV.1.ne'
   have ht': f U/V - L v=Q*a:=by
       have hr:Q*(V*a)= f U + V*L (-v):=by rw [← show P.density _ _ _ _=_ from hV.2]; refine (congr_fun hk U).trans ?_; change f U+Q* (parcel C d k N p (-v)).density 0 Y! (R k) U=_; rw [(allzeroes C N p k d (parcel C d k N p (-v)) U h).2]; unfold L Spindle.awakeFull; rw [mul_left_comm]
       rw [hA] at hr; field_simp; linear_combination -hr
   change ‖f U/V-L v‖≤_; rw [ht',norm_mul,show ‖Q‖=(C.S.a k^d)⁻¹ from by unfold Q pinHat; rw [norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]]
   let Y:=(C.path.levels.params k).columns
   have hCl:(R k).p=point C k:=(H.wilson.represents N p k hx).vac
   have hQ:1≤ Y:=((T).levels.params _).columns_ge
   have hv':= hull (C.localSection d) (R k) 0 P U (C:=Y) (fun i=>by change (R k).p.Regular _ _ ∧ (R k).p.supBounds _ _ _ (_ * (R k).p.threshold^_); rw [hCl]; exact H.priced d k p ht 0 i) hv (divisor_le ..) (zero_le_one.trans hQ)
   rw [mul_comm,← div_eq_mul_inv]; refine div_le_div_of_nonneg_right (hv'.trans ?_) (pow_pos (C.S.a_pos _) _|>.le)
   linarith only [mul_le_mul_of_nonneg_left he (show 0 ≤ 1+Y by linarith only [hQ]),mul_nonneg (show 0≤Y from zero_le_one.trans hQ) (rem_nonneg hv)]
end
end YM.MergeProof
