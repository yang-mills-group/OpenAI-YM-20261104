import YM.OPE.Coverage.Signage
import YM.OPE.Coverage.TrackSales
/-!
## Bound the flux coefficient on every sufficiently supplied finite shelf curve,
without spending estimates across infinitely many geometric steps.
-/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 4000000
noncomputable section
namespace YM.OPE.Coverage
open Function Set Filter Extraction Climb Ward Table Org Maxwell Spec Next.UVStress Extra
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open WeakScaling
variable {G : Gauge}{C:Family G}{S:Table C.book}{F:Order}{V:DiffPlan S}{T:Lighthouse C.book}{h':Extraction.Order}
set_option quotPrecheck false
local notation "T₀" => Bel C.book


variable {M D d N m:ℕ}{Q R:ℝ}{V:DiffPlan S} -- notation remove
variable {MD:MaxwellData C}{H:S.Hierarchy}{J:S.Stress}{Y : Ward.SpinRows S}
variable (b : Curve V MD.T.W H.spin MD.hT.spin M D Q) --  -- placeholder
local notation "𝗋" => b.r
lemma orientation_affords (W : Lighthouse C.book)(b:Curve V W.W H.spin MD.hT.spin M D Q) (hi : 1 ≤ R)(hQ:R < Q)(hN:max N 1 ≤ M)(hD : max d 4 + m < D)
     (hV : V.Derivatives S) (hW : W.W.Derivatives (Bel C.book))
     (pass : ∀ X : Scaling S, Track X V W J H.spin MD.hT.spin N d m R → Tendsto (fun i=>(X.xi i)⁻¹) atTop (𝓝 W.κ))
     {c:ℝ}(hc:0 < c)(hJ: J ≠ 0){σ:ℕ→ℕ}(hs:Tendsto σ atTop atTop) (he:Tendsto (b.micro J ∘ σ) atTop (𝓝 (c • W.J))) :
     ∃ B:ℝ,∀ᶠ i in atTop, ‖b.pull J (σ i)‖*(b.r (σ i))^4 ≤ B :=by
       let f(i):=‖b.pull J (σ i)‖ * (b.r (σ i))^4
       by_contra! hz
       choose s hs_m hB using fun i:ℕ=> frequently_atTop.mp (hz i) i
       have hf:=tendsto_atTop_mono (f:=fun i:ℕ=>(i:ℝ)) (g:=fun j=>f (s j)) (fun i=> (hB i).le) tendsto_natCast_atTop_atTop
       have he':= (tendsto_const_nhds (x:=(1:ℝ)) |>.div_atTop (hf.const_mul_atTop hc))
       obtain ⟨X,hTr,hl⟩: ∃ X:Scaling S,Track X V W J H.spin MD.hT.spin N d m R ∧ ∀ᶠ i in atTop, (X.xi i)⁻¹ < |W.κ|/2 := by
           have hw:Tendsto s atTop atTop:=tendsto_atTop_mono (f:=id) (fun i : ℕ=>hs_m i) tendsto_id
           apply b.tracks_cal hi hQ (p:=fun r=>r⁻¹ < |W.κ|/2) ((le_max_left ..).trans hN) (N:=N) (d:=d) (m:=m) (by omega) (by omega) H hV MD.hT hW hJ (hs.comp hw) hc (he.comp hw)
           filter_upwards [he'.eventually (gt_mem_nhds (half_pos (abs_pos.mpr W.hκ)))] with i hi
           change 1/(c*f (s i))< _ at hi
           dsimp only [comp_apply]; simpa [f,one_div, mul_assoc] using hi

       apply not_le_of_gt (half_lt_self (abs_pos.mpr W.hκ)); exact le_of_tendsto (pass X hTr).abs (hl.mono (fun i hi=> by change |(X.xi i)⁻¹|≤_; rw [abs_of_pos (inv_pos.mpr (X.sign _))]; exact hi.le))
theorem unique_ξ {V : DiffPlan S}{MD:MaxwellData C} (hA : FreeDiv MD.T MD.hT MD.lit.hers)(ht: V.Inclusions S)(hD: V.Derivatives S)
    {H:S.Hierarchy}{J:S.Stress}{Y}(hJ:J ≠ 0)(A:Pre H V J V.deriv Y)(hC:Centered J):
     ∃ (D N m:ℕ) (R:ℝ), 1 ≤ R ∧ ∀ {d n:ℕ}{Q:ℝ}(b:Curve V MD.T.W H.spin MD.hT.spin n d Q), max D 4 + m < d → 1 ≤ n → N ≤ n → R<Q → ∃ B:ℝ,∀ᶠ k in atTop,‖b.pull J k‖*(b.r k)^4 ≤ B :=by
     let s : IR (C:=C) S:=⟨J,V.deriv,Y⟩
     have hh(P:MaxwellData C):=tracks_ratio P (I:=s) H ht hD A (c:=1) ((one_smul ..).symm)
     obtain ⟨D,N,m,R,hR,hf⟩:= (hh MD).ask
     obtain ⟨d,n,ℓ,P,hP,ha⟩:= (hh (WeakScaling.negative MD)).ask
     refine ⟨max D d,max N n,max m ℓ,max R P,?_,?_⟩
     · exact hR.trans (le_max_left ..)
     intro d' n' Q b hd' hN hN' hQ
     let f(k):= ‖b.pull J k‖*(b.r k)^4
     by_contra! hz
     choose u hu ht' using fun i:ℕ=> frequently_atTop.mp (hz i) i
     have hs:Tendsto u atTop atTop:=tendsto_atTop_mono (f:=id) hu tendsto_id
     haveI : ProperSpace ((Free C).Stress) := FiniteDimensional.proper ℂ _
     obtain ⟨p,hp,σ,hσ,hj⟩ := (isCompact_closedBall (0 : (Free C).Stress) 1).tendsto_subseq
       (fun k => show b.micro J (u k) ∈ Metric.closedBall _ _ by simp [Curve.micro_norm _ hJ ..])
     have he : ‖p‖ = 1 := tendsto_nhds_unique hj.norm ((tendsto_const_nhds (x:=(1:ℝ))).congr fun i=> (Curve.micro_norm b hJ (u (σ i))).symm)
     have hu':= hs.comp hσ.tendsto_atTop
     obtain ⟨h₁,h₂,h₃⟩ := b.survives (((zero_lt_one.trans_le hR).trans_le (le_max_left ..)).trans hQ : 0<Q) (by omega : 4 < d') (by omega) H hD (J:=J) A.tensor A.symmetric hC hu' hj
     obtain ⟨c,hc'⟩ := charge_line hA _ h₁ h₂ h₃
     have h_c : c ≠ 0 := by rintro rfl; simp [hc'] at he
     have ht'ξ : Tendsto (fun k=>(σ k:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop
     have hσ' : ¬ ∃ B:ℝ, ∀ᶠ k in atTop, f (u (σ k)) ≤ B := by
        rintro ⟨a,ha⟩
        obtain ⟨k,hi,hk⟩:= (ha.and (ht'ξ.eventually_ge_atTop a)).exists
        exact not_lt_of_ge hi (hk.trans_lt (ht' (σ k)))
     apply hσ'
     rcases h_c.lt_or_gt with hc|hc
     · have he' : Tendsto (b.micro J ∘ u ∘σ) atTop (𝓝 ((-c) • (WeakScaling.flip MD.T).J)):=by
            rw [show ((-c) • (WeakScaling.flip MD.T).J) = p from by
              change (-c) • (-MD.T.J) = p
              rw [hc', _root_.neg_smul, _root_.smul_neg, neg_neg]]
            exact hj
       exact orientation_affords (WeakScaling.flip MD.T) (MD:=MD) (H:=H) (show Curve V (flip MD.T).W H.spin MD.hT.spin n' d' Q from b) (N:=n) (d:=d) (m:=ℓ) (R:=P) hP ((le_max_right ..).trans_lt hQ) (by omega) (by omega) hD MD.lit.pales (fun X H' =>(ha X _ _ _ _ le_rfl le_rfl le_rfl le_rfl H').congr (fun i=> one_div _)) (neg_pos.mpr hc) hJ hu' he'
     have he' : Tendsto (b.micro J ∘ u ∘σ) atTop (𝓝 (c • MD.T.J)):=by rwa [← hc']
     exact orientation_affords MD.T (MD:=MD) (H:=H) b (m:=m) (N:=N) (d:=D) hR ((le_max_left ..).trans_lt hQ) (by omega) (by omega) hD MD.lit.pales (fun X H' =>(hf X D N m R le_rfl le_rfl le_rfl le_rfl H').congr (fun i=> one_div _)) hc hJ hu' he'
end YM.OPE.Coverage
