import YM.PhysMS.Frame.Apply

/-! Transfer to the measured readings before any phase is fixed. Costs without
an exceptional set. Extends phase_jets_flat through the continuously calibrated
frames (no reuse/exchange of spacing costs across different constructions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Filter Set Spec OPE OPE.Orbits Climb Trace.Pilot
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U:ℝ→tower S)(H:Leading F U)(h:G.Simple)(X:Scaling S)(hu:Foundation F R)
    {n : ℕ}{d:Caps n}

-- measured price via rate envelope.
local notation "Q" => F.sector.derivatives
set_option quotPrecheck false
local notation "pr" => Φ

def jet (j:ℕ) (v:Viewers F)(d:Caps n)(r:ℝ)(x:Points n):=
    positionsJet S (spectator F v) (spectate F v).smooth d j r x

lemma jet_rises (j:ℕ) {r:ℝ}(p:Viewers F){d e:Caps n}(he:d≤e)(v:Labels S d){x:Points n}(hx:x∈conf n)(hr:0<r): jet F j p d r x v= jet F j p e r x (fun t=>(Q).rise (he t) (v t)) := by
   unfold jet; have hv:=Work.A05.smul_conf hr hx; rw [positions_at (h:=hv),positions_at (h:=hv)] -- syntax
   refine ((?_ : (fun y=> S.classMoment (spectator F p) d (r • y) v) =ᶠ[𝓝 x] _).iteratedFDeriv ℝ j).eq_of_nhds
   filter_upwards [(conf_open _).mem_nhds hx] with y hy
   have hf := Work.A05.smul_conf hr hy
   have h₀(d : Caps n)(v:Labels S d):= point_moment F p (Orbits.tags v) hf
   exact (h₀ d v).trans ((Levy.inclusionMoment F d e he v (r • y).ofLp p hf).trans (h₀ e _ |>.symm))

lemma jet_from_measure (q : Viewers F)(r:ℝ)(U:tower S)(v:MaxwellSlots C d)(j:ℕ){x:Points n}(h:r • x∈conf n) :
    jet F j q d r x (fun t=>U (d t) (v t)) = iteratedFDeriv ℝ j (measured F q U v r) x := positions_at S _ _ d j r x h _

lemma jet_values (j:ℕ) (v:PhysMS.Word (C:=C) S n) (p:Viewers F) {r:ℝ}{x:Points n}(hx:x∈conf n)(hr:0<r) :
    iteratedFDeriv ℝ j (value F p v r) x = (r^charge v) • jet F j p _ r x (Nesting.voices v) := by
    have hk := Work.A05.smul_conf hr hx
    unfold jet; rw [positions_at (h:=hk)]; exact iteratedFDeriv_const_smul_apply'
      ((((S.class_smooth _ (spectate F p).smooth v).contDiffAt ((conf_open n).mem_nhds hk)).comp (f:=fun y:Points n=>r • y) x (contDiffAt_id.const_smul r)).of_le (WithTop.coe_le_coe.mpr le_top))

variable (M η ε:ℝ)(hM:0≤M)(hη:0<η)
private abbrev domain (M η:ℝ):Set (Points n):=fun x=>WithinRoom 1 M η x.ofLp 0

section
variable {J:Type} {l:Filter J} {r:J→ℝ} (hr:Tendsto r l trail) (p q:J→Viewers F)
variable (x:J→Points n)(hx:∀ᶠ i in l,x i∈domain M η)
include R X hM hη hu hr hx h
lemma jets_points (j:ℕ)(d:Caps n)(v:Labels S d) : RateLE l (LogV ∘ r)
    (fun i=> (jet F j (p i) d (r i) (x i)-jet F j (q i) d (r i) (x i)) v) (weight d-4):=by
    let P:= Orbits.tags v
    let b i:=jet F j (p i) d (r i) (x i) v-jet F j (q i) d (r i) (x i) v
    -- unscale with normalization r^sum d. Use the exact Length rate.
    let A i:= (r i)^charge P • b i; have hv: RateLE l (LogV ∘ r) A (-4) := by
        intro t ht; let c:ℝ:= (Fintype.card (Fin n × Axis):ℝ)^j*2
        let δ:=(t+4)/2; have he:0<δ:=by unfold δ; linarith only [ht]
        have hf:= RateLE.const c (to_log_zoom.comp hr) |>.mul ((length_rate.rpow (4-δ)).comp hr|>.pays (to_log_zoom.comp hr))
        have hA:= (hf.of_norm_le (F:=A) ?_) -- name?
        swap
        · filter_upwards [hr.eventually (phase_jets F R X h hu P hM hη he j), hr.eventually (show ∀ᶠ i in trail, 0 < i from self_mem_nhdsWithin),hx] with i hi hp hx
          have hx':= conf_room hη hx; specialize hi (x i) hx (p i) (q i); rw [iteratedFDeriv_sub_apply ((value_tied F (p i) P hp hx').of_le (WithTop.coe_le_coe.mpr le_top)) ((value_tied F (q i) P hp hx').of_le (WithTop.coe_le_coe.mpr le_top)),jet_values F j P _ hx' hp,jet_values F j P _ hx' hp,← smul_sub, ← mul_assoc] at hi; exact hi
        apply hA _ ?_; dsimp only [δ]; linarith
    have hB:=(((length_rate.power (charge P)).inv).comp hr).pays (to_log_zoom.comp hr) |>.smul hv
    have he : (charge P:ℝ)=weight d:=charge_eq P
    rw [he,mul_neg,mul_one,neg_neg, ← sub_eq_add_neg] at hB
    refine hB.congr ?_; filter_upwards [hr.eventually (show ∀ᶠ i in trail, 0 < i from self_mem_nhdsWithin)] with i hi using inv_smul_smul₀ (pow_ne_zero _ (ne_of_gt hi)) _
include H
lemma dynamic (j:ℕ)(v:MaxwellSlots C d) : RateLE l (LogV ∘ r)
   (fun i=> iteratedFDeriv ℝ j (measured F (p i) (U (r i)) v (r i)) (x i)-iteratedFDeriv ℝ j (measured F (q i) (U (r i)) v (r i)) (x i)) (-4):=by
     let M0 i d:= (jet F j (p i) d (r i) (x i)-jet F j (q i) d (r i) (x i)); have ht:= hx.and (hr.eventually (show ∀ᶠ i in trail, 0 < i from self_mem_nhdsWithin))
     have hp:= total F R U H hr v (-4) M0 (fun e he=>ht.mono fun i hi v=> congr_arg₂ HSub.hSub (jet_rises F j (p i) he v (conf_room hη hi.1) hi.2) (jet_rises F j (q i) he v (conf_room hη hi.1) hi.2)) (fun e _ u=> jets_points F R h X hu M η hM hη hr p q x hx j e u) -- M shadow
     exact hp.congr (ht.mono fun i hi=> congr_arg₂ HSub.hSub (jet_from_measure F _ _ _ _ j (Work.A05.smul_conf hi.2 (conf_room hη hi.1))) (jet_from_measure F _ _ _ _ j (Work.A05.smul_conf hi.2 (conf_room hη hi.1))))
end
include H h X hu
lemma within_price (j:ℕ)(v:MaxwellSlots C d) (he:0<ε) (hM:0≤M) (hη:0<η) : ∀ᶠ r in trail, ∀ x:Points n,WithinRoom 1 M η x.ofLp 0→ ∀ p q : Viewers F, ‖iteratedFDeriv ℝ j (measured F p (U r) v r) x - iteratedFDeriv ℝ j (measured F q (U r) v r) x‖ ≤ r^(4-ε):= by
   let V:=Points n × Viewers F × Viewers F
   let P := fun (_:ℝ)(x:V) => x.1∈domain M η
   let D := fun (r:ℝ)(x:V)=> iteratedFDeriv ℝ j (measured F x.2.1 (U r) v r) x.1 - iteratedFDeriv ℝ j (measured F x.2.2 (U r) v r) x.1
   have H:= uniform_power (P:=P) (m:=4) (Y:=D) he (fun u l hl hL ht=>dynamic F R U H h X hu M η hM hη (show Tendsto id l trail from tendsto_id.mono_left hL) (fun x=>(u x).2.1) (fun x=>(u x).2.2) (fun x=>(u x).1) ht j v)
   filter_upwards [H] with r hr x hx p q using hr (x,p,q) hx

/-- Same frames and any calibrated leading-log coupling; the EACH-character comparison for
    all measured multiple-insertion separated correlations (no other/macroscopic
    spectators in this statement) reduces to unselected comparison with the target answer. -/
theorem negligible (j:ℕ)(v:MaxwellSlots C d)(s:Set (Points n))(hs:IsCompact s)(hK:s⊆conf n) (g:ℝ→ℝ)(hg:Coupling G g)(a:ℝ)(ha:0<a)(N:ℕ) :
    ∀ᶠ r in trail, ∀ x∈s, ∀ p q : Viewers F, ‖iteratedFDeriv ℝ j (measured F p (U r) v r) x - iteratedFDeriv ℝ j (measured F q (U r) v r) x‖ ≤ a * g r ^ N := by
   obtain ⟨M,hM,η,hη,hV⟩:= compact_within s hs hK; filter_upwards [within_price F R U H h X hu M η 1 j v zero_lt_one hM hη,subpower_payment hg h 1 (4-1) (by norm_num) a ha N] with r hr hp x hx p q; exact (hr _ (hV x hx) p q).trans ((one_mul _).symm.le.trans hp)

-- In particular genuine leading comparison on all characters at once (no asserted positive-order
-- rate of convergence of the unselected signal here). Inputs include Lie & gauge as in the history.
theorem all_leading (j:ℕ)(v:MaxwellSlots C d)(s:Set (Points n))(hs:IsCompact s)(hK:s⊆conf n) (ε:ℝ)(he:0<ε) :
    ∀ᶠ r in trail, ∀ x∈s, ∀ p : Viewers F, ‖iteratedFDeriv ℝ j (measured F p (U r) v r) x - iteratedFDeriv ℝ j (WickGoal v) x‖ < ε := by
   let δ:=ε/2; have hδ:0<δ:= half_pos he; obtain ⟨M,hM,η,hη,hV⟩:= compact_within s hs hK; have hp : Tendsto (fun r:ℝ=> r^((4:ℝ)-1)) trail (𝓝 0):= length_rate.rpow (4-1) |>.tends (by norm_num) to_log_zoom
   filter_upwards [within_price F R U H h X hu M η 1 j v zero_lt_one hM hη,hp.eventually (ge_mem_nhds hδ),Metric.tendstoUniformlyOn_iff.mp (H.lead _ _ v j s hs hK) δ hδ] with r h₁ he h₂ x hx i; specialize h₂ x hx; rw [dist_comm,dist_eq_norm] at h₂; apply (norm_sub_le_norm_sub_add_norm_sub _ (iteratedFDeriv ℝ j (measured F none (U r) v r) x) _).trans_lt; exact (add_halves ε) ▸ add_lt_add_of_le_of_lt ((h₁ x (hV x hx) i none).trans he) h₂
end YM.PhysMS.Frame
