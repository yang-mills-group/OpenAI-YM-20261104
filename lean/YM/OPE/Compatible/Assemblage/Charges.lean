import YM.OPE.Compatible.Assemblage.Guided
/-!
# Between matched levels: expose admissible single costs to the crew
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge}{H:History G}{E:Hol G}{N p i d k j:ℕ}{F:Labels.Frame G d}(Z:SectionData F)
variable {D:∀ N p i:ℕ,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i)} {w v ζ ψ:ℕ→ℝ}
set_option quotPrecheck false
variable {Q:∀ i:ℕ, Coefficient F (H.S.side i p)}{W:Bid.Worth}
-- supplementary simpler motion prices. build Travels
lemma wake_earned (hw:∀ i:ℕ,k ≤ i→ i ≤ N→ 0<w i)(hc:∀ i:ℕ,k ≤ i→ i<N → w (i+1) ≤ w i) (hQ:Fiesta H F ζ ψ k)(M:Extra.Histories.Music F H N p)(X:F.Coeff)
    (hS:Sung Z H N p E W k M)(he:∀ i:ℕ,k ≤ i→ ∀ hi:i<N, Carol Z H N p i (D N p i hi) (M.tone (i+1)) (M.tone i) (ψ i))
    (hL:∀ i:ℕ,k ≤ i→ i≤ N→ w i * bond H N p M i X ≤ ζ i):
    Guided Z E H N p k N (fun i=>(M.tone i).plays X) D w:=by
    refine ⟨hS.ahead,le_rfl,hw,fun i hi hp=>?_,fun i hi hp=>?_,fun i hi hp=> (hS.step i hi hp).values X,fun i hi hp=>?_⟩
    · exact ⟨((hS.earned i hi hp).earns X).1, _,((hS.earned i hi hp).earns X).2⟩
    · have ht:= hL i hi hp; let x:=(M.tone i).index X; have hz: w i*‖alto H i d*x 0‖ ≤ w i*bond H N p M i X :=by
           rw [norm_mul]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hw i hi hp|>.le); change ‖x 0‖ ≤ ∑ j:F.Index,‖x j‖; exact single_le_sum (fun i _=> norm_nonneg (x i)) (mem_univ 0)
      change w i*‖alto H i d* ((M.tone i).plays X).x 0‖ ≤ _; rw [(hS.earned i hi hp).currents]
      exact hz.trans (ht.trans ((le_mul_of_one_le_right ((mul_nonneg (hw i hi hp|>.le) (norm_nonneg _)).trans (hz.trans ht)) (H.levels.params i|>.columns_ge)).trans (hQ.coin i hi)))
    obtain ⟨p0,hp₀,hP⟩:= he i hi hp; have he:=hP X
    have hi':=hi.trans i.le_succ; obtain ⟨hX,hx⟩:= cost_step H E Z ζ ψ k N p M i X _ _ (hL _ hi hp.le) (hw _ hi hp.le|>.le) (hw _ hi' hp|>.le) hQ (hc i hi hp) hi (hL _ hi' hp) (hS.earned i hi hp.le)
    refine ⟨p0,hp₀,_, (M.tone i).charge X,hx,hX,(hS.earned i hi hp.le|>.earns X).2,?_⟩
    rw [(hS.earned _ hi' hp).currents X]; exact he
lemma singing {hN:j ≤ N}(hk:k ≤ j)(hw:∀ i:ℕ,k ≤ i→ i ≤ j→ 0<w i)(hc:∀ i:ℕ,k ≤ i→ i<j → w (i+1) ≤ w i) (hQ:Fiesta H F ζ ψ k)
    (h:Club H E Z ζ ψ k j N p w D Q v hN): Guided Z E H N p k j Q D w:=by
    have hz (i:ℕ)(hk:k ≤ i)(ht:i ≤ j):(w i*‖alto H i d‖)*(F.coeffSize (Q i).x) ≤ ζ i:=
       (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (rem_nonneg ((h.ticks i hk ht).2))) (mul_nonneg (hw i hk ht|>.le) (norm_nonneg _))).trans (h.rates i hk ht)
    refine ⟨hk,hN,hw,fun i hk ht=> ⟨(h.ticks i hk ht).1,v i,(h.ticks i hk ht).2⟩,fun i hk ht=> ?_,fun i hi hp=>(h.votes i hi hp).1,fun i hi hp=>?_⟩
    · let x:=(Q i).x; have he:=hz i hk ht; have hζ:0≤ζ i:= le_trans (mul_nonneg (mul_nonneg (hw i hk ht|>.le) (norm_nonneg _)) (Work.G08.size_nonneg ..)) he
      rw [norm_mul,← mul_assoc]; apply le_trans _ (he.trans ((le_mul_of_one_le_right hζ (H.levels.params i|>.columns_ge)).trans (hQ.coin i hk))); refine mul_le_mul_of_nonneg_left (show ‖x 0‖≤ ∑ j:F.Index,‖x j‖ from single_le_sum (fun i _=> norm_nonneg (x i)) (mem_univ 0)) (mul_nonneg (hw i hk ht|>.le) (norm_nonneg _))
    obtain ⟨_,p',hF,hP⟩:= h.votes i hi hp; let u:= i+1; have hu:k ≤ u:=hi.trans i.le_succ
    refine ⟨p',hF,_,_,?_,?_,(h.ticks i hi hp.le).2,hP⟩
    · let γ:= (H.levels.params (i+1)).columns; let f:=(orbitCost F)*(ψ i+2*γ); let Y:=‖alto H u d‖; have hy:0 ≤ Y:= norm_nonneg _
      have he:f ≥ 2:=by have ht:= orbitCost_one_le F; have hh:1 ≤γ:= (H.levels.params (i+1)).columns_ge; unfold f; nlinarith only [ht,hh,hQ.tap i hi]
      have hx: Relay.weighted H F (ψ i) u (Q u).x (v u) ≤ f*(v u+F.coeffSize (Q u).x):=by unfold Relay.weighted; have ht:= mul_le_mul_of_nonneg_right he (rem_nonneg ((h.ticks _ hu hp).2)); unfold f γ u at *; linarith only [ht]
      refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hy) (mul_nonneg zero_le_two (hw u hu hp|>.le))) ?_
      have hv:= mul_le_mul_of_nonneg_left (h.rates u hu hp) (show 0 ≤ 2*f by linarith only [he]); change 2*w u*(Y*(f*(v u+_))) ≤ _; change 2*f*(w u*Y*(v u+F.coeffSize _)) ≤ _ at hv
      linarith only [hv,(show 2*f*ζ u≤ 1 from by unfold f; rw [← mul_assoc]; exact hQ.room i hi)]
    have ht:w i*‖alto H i d‖* v i ≤ ζ i:= le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Work.G08.size_nonneg F (Q i).x)) (mul_nonneg (hw i hi hp.le|>.le) (norm_nonneg _))) (h.rates i hi hp.le)
    have he:0 ≤ v i:= rem_nonneg ((h.ticks i hi hp.le).2); have hh:0 ≤ ζ i:= le_trans (mul_nonneg (mul_nonneg (hw _ hi hp.le|>.le) (norm_nonneg _)) he) ht
    exact (mul_le_mul_of_nonneg_right (hc i hi hp) (mul_nonneg (norm_nonneg _) he)).trans ((le_trans (le_of_eq (Eq.symm (mul_assoc ..))) ht).trans ((le_mul_of_one_le_right hh ((H.levels.params i).columns_ge)).trans (hQ.coin i hi)))
end YM.MergeProof.Ribbons.ManyCopies.Stem
