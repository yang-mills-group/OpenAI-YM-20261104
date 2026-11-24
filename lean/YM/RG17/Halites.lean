import YM.RG17.Conductor
/-! All-sector singles and entire path of horizon0 discrepancy, no intermediate Gram prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent Relay MergeProof.Float PhysicalNext.Repeat Lotus GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N p k m:ℕ)(H:C.Makes)
variable {W:Worth}{w ψ ζ:ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "T"=> C.path
local notation "ℓ"=> C.ref 0
local notation "F"=> C.labels.level 0
local notation "Y!"=> C.localSection 0
local notation "s!"=> C.factory 0 N p
local notation "R"=> C.path.rep N p
local notation "ρ"=> liftVac C.path N p
section
variable (X:Extra.Histories.Music (C.labels.level 0) C.path N p) {m:ℕ}{Z:∀ i:ℕ,Coefficient (C.labels.level 0) (C.side i p)}{φ:ℕ→ℝ} {hk:k ≤ N} (h:Club C.path C.params (C.localSection 0) ζ ψ m k N p w D Z φ hk) (hX:Sung (C.localSection 0) C.path N p C.params W (C.ref 0) X) (hG:G.Simple)
    {j:ℕ} (hx:m ≤ j)
include h hx
lemma dispatchLine (hy:j ≤ k): (Z j).density 0 Y! (R j)=pushTo T N p hy ((Z k).density 0 Y! (R k)):=by
   induction hy using Nat.decreasingInduction with
   | self=> rw [pushTo_self]
   | of_succ i hi ih=>
      rw [(h.votes i hx hi).1, ih (hx.trans (Nat.le_succ i)),blast,pow_zero,one_smul]
      rw [← pastPass T N p (Nat.le_succ i) hi,pushTo_next T N p (le_refl i),pushTo_self]
omit h hx
include H hG hX
lemma lampLine (b:(C.labels.level 0).Coeff) (hy:ℓ ≤ j) (hV:j ≤ N): ((X.tone j).plays b).density 0 Y! (R j) = RG17.send0 C ((s!).terminal b) • (ρ j):=by
   induction hV using Nat.decreasingInduction with
   | self=> funext U; have hv:=congr_fun (capZero C N p H hG hy ((s!).terminal b)) U
            rw [hX.head.earns b U,pow_zero,one_mul]; change TransferData.cylinder _ _ _ _ U=_ at hv; rw [TransferData.cylinder,LinearEquiv.symm_apply_apply] at hv
            rw [hv]; exact mul_comm .. -- syntax
   | of_succ i hi ih=>
      rw [(hX.step i hy hi).values b, ih (hy.trans (Nat.le_succ i)),blast,pow_zero,one_smul,StepData.push_smul _ _ _ _ (vac_integrable T N p (i+1) H.wilson hi),vac_transfer T N p i H.wilson hi]
end
-- one-step helper pushTo step.
section
variable {φ:ℝ}{Q:Coefficient (C.labels.level 0) (C.side k p)}
lemma shiningOne (hr:Q.Format 0 C.params (R k)) : Q.density 0 Y! (R k) 1= ρ k 1*(Q.x 0) := by
     let U:Config G (C.side k p):=1; have he:flags (R k).p.threshold U=∅:= UVNext.CouplingReset.flags_one _
     have hv(i): Q.marked (R k) i U=0:=by
        unfold Coefficient.marked; split
        next hp=> by_cases h:i=∅; rw [h,Finset.sum_empty]; obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr h; obtain ⟨x,hx⟩:= ((R k).activities.forced j).inventory_ne; have hY:x∈flags (R k).p.threshold U:=hp.2 ▸ mem_biUnion.mpr ⟨j,hj,hx⟩; rw [he] at hY; exact absurd hY (Finset.notMem_empty _)
        next _=> exact rfl
     have hZ(i): Q.maskedTerm (R k) i U=0 :=by
        unfold Coefficient.maskedTerm masked Set.indicator; split
        next h=> exact hr.identity_null i
        next h=>exact rfl
     have ha: (Y!).places ((F).scaled (R k).p.threshold⁻¹ ((F).core Q.x)) (0:Site _) U=0:=by
        have hT:= Ribbons.ManyCopies.Cadet.Studio.ZeroDegree.one_core Q.x; rw [hT,map_zero,SectionData.places]; exact congr_fun ((Y!).eval_linear.mk' (Y!).evaluate|>.map_zero) _ -- levels? footprint
     change Q.density 0 (C.localSection 0) (R k) U = _; unfold Coefficient.density Coefficient.exponentialEntry
     simp only [hZ,hv, tsum_zero,add_zero,mul_zero,add_zero]; unfold masked Set.indicator; split
     next h=> rw [ha, add_zero]; rfl
     next h=> simp [liftVac,U] -- rewrite zero
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
lemma turnIn {w: Site (C.side J p)→ℝ}{a e:ℝ} (hr:Q.Format 0 C.params (R k))(hc: Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) φ) (hf:Continuous f) (hZ:Served (R k) (fun i=> radiant (alto T k 0) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k 0)) (gust T N p N (M') k hk) (o k) w a e) : pushTo T N p hk (fun U=> ρ N U*f U) = Q.density 0 Y! (R k):=by
    let Θ:=gust T N p N (M') k hk
    have ht : (fun U=> ((M') U).part ((Bt).fire 0))=(fun U=> ρ N U*f U):= funext fun U=> by
       rw [boot]; change _* (U').copy 0 f U=_; rw [show (U').copy 0 f=f from Ribbons.cappid C J p N (hJ.trans hk) (fun _=> f) true]; rfl
    have hh : Integrable (M') (prior G _):= (hatCont C N p (fun i=> (U').copy i f) (fun i=> Ribbons.cappedC C J p N (hJ.trans hk) (fun _=> f) (i,true) hf) (by rw [(H.wilson.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    choose K hF hK hh' using fun i:Site (C.side J p)=>sparkling T _ Y! Q (u' i) (o k i) (alto T k 0) H.wilson 0 hk (H.sections _) hr hc
    rw [show (fun i => sunny _ _ _ _ _)=fun i=>profile (R k).activities (K i) from funext hF] at hZ
    rw [← ht,← gust_choose T N p (M') hh hk]; funext U; rw [(hZ.relay hK (H.wilson.represents N p k hk).good.labels U).1 (0:V),hh', radiant,handmove C k p J hJ,alto,pow_zero, inv_one,one_smul]; exact congr_fun (Ribbons.cappid C J p k hJ (fun _=>_) true) U
end
section
variable (X:Extra.Histories.Music (C.labels.level 0) C.path N p) {Z:∀ i:ℕ,Coefficient (C.labels.level 0) (C.side i p)}{γ:ℕ→ℝ} {hk:k ≤ N} (h:Club C.path C.params (C.localSection 0) ζ ψ m k N p w D Z γ hk) (hX:Sung (C.localSection 0) C.path N p C.params W (C.ref 0) X) (hG:G.Simple)
    (b:(C.labels.level 0).Coeff) (f:Config G (C.side N p)→ℂ)
local notation "l'"=> (X.tone k|>.plays (-b))
include H h hX hG
lemma brilliant (hn:C.ref 0 ≤ m) (hr:Q.Format 0 C.params (R k))(hc: Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) φ) (ht:(Z k).exponentialEntry 0 Y! (R k)= Q.exponentialEntry 0 Y! (R k)+(l').exponentialEntry 0 Y! (R k))(hK:profile (R k).activities (Z k).forced=profile (R k).activities Q.forced + profile (R k).activities (l').forced) (he:pushTo T N p hk (fun U=>ρ N U*f U) = Q.density 0 Y! (R k)) (j:ℕ) (hm:m ≤ j)(hj:j ≤ k) : (Z j).density 0 Y! (R j)= pushTo T N p (hj.trans hk) (fun U=> ρ N U*f U)+ (-(RG17.send0 C ((s!).terminal b))) • ρ j ∧ pushTo T N p (hj.trans hk) (fun U=>ρ N U*f U) 1 / ρ j 1 - RG17.send0 C ((s!).terminal b)=(Z j).x 0 := by
   have hl:=hm.trans hj; have ha:=hn.trans hl; let y:=RG17.send0 C ((s!).terminal b); have hY:(l').density 0 Y! (R k)=(-y) • ρ k:=by rw [lampLine C N p H X hX hG (-b) ha hk,map_neg,map_neg]
   have hp:=(hX.earned k ha hk).earns (-b); have hL:=(H.wilson.represents N p k hk).good
   have hF:(Z k).density 0 Y! (R k)= Q.density 0 Y! (R k)+(-y) • ρ k:=by
        rw [← hY, ← Relay.plus hL hc hp.2,← coin_primary,← coin_primary]; rw [ht,← duo_exp Y! hc hp.2]; exact coin_port _ _ (rem_dominated ((h.ticks k hl le_rfl).2)) (rem_dominated ((presentation hr hc hp.1 hp.2).2)) (hK.trans (duo_profile hc hp.2).symm) hL.labels
   have hG:(Z j).density 0 Y! (R j)= pushTo T N p (hj.trans hk) (fun U=> ρ N U*f U)+(-y) • ρ j:= by rw [dispatchLine C N p k h hm hj,hF,canvasBills T N p H.wilson hj hk _ _ (play_integrable T N H.wilson hk hr hc),← he,pastPass T N p hj hk]
   constructor; exact hG
   have hv:= shiningOne C N p j ((h.ticks j hm hj).1); rw [hG] at hv
   let v:= liftVac T N p j 1
   have h':v≠0:=by unfold v liftVac; rw [Rep.eval,Activities.gas_one _ _ (UVNext.CouplingReset.flags_one _),mul_one, Complex.ofReal_ne_zero]; exact (Real.exp_pos _).ne' -- `ne_zero` lemma?
   let a':= pushTo T N p (hj.trans hk) (fun U=> ρ N U*f U) 1
   let q:=(Z j).x 0; change a'+(-y)*v=v*q at hv; change a'/v-y=q
   field_simp; linear_combination hv
end
end
end YM.MergeProof
