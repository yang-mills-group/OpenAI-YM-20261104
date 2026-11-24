import YM.OPE.Compatible.Eyrie.Return
import YM.OPE.Compatible.Eyrie.Birds
/-! # Local null boundary comparison -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Eyrie
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid
open Extra.Histories MergeProof MergeProof.Accent Push.GridApprox RigE Owl
open scoped Topology Classical BigOperators
variable {G:Gauge}{n:Side}{l k p N r m:ℕ}{C:Family G}{f:Extraction.Order}(H:C.Makes)
lemma puffInt (F:lots G (C.side N p)) (h:Continuous F)(hk:k ≤ N)(l:ℕ): Integrable (OPE.Eyrie.puff C.path N p l F hk) (prior G (C.side k p)):= (pushTo_integrable C.path N p hk _ (soot C.path _ h)).smul _
lemma sale (F M:lots G (C.side N p))(h:Continuous F)(ht:Continuous M)(hp:k≤N)(l:ℕ): puff C.path N p l (F-M) hp= puff C.path N p l F hp-puff C.path N p l M hp:=by
        rw[sub_eq_add_neg,WaveF C.path hp _ _ h ht.neg]; rw [←neg_one_smul ℂ M,Opal C.path hp _ ht]; rw [neg_one_smul,sub_eq_add_neg] -- check last occurrence
lemma costV {b:ℝ}(S E J:lots G n)(hh: Integrable S (prior G n))(he:Integrable E (prior G n))(hp:Envelope J)(hm:πfee S J=0)(hv:∀ U,‖E U-S U‖ ≤ b): ‖πfee E J‖ ≤ b*γfee J:=by
        obtain ⟨v,h⟩:= hp.cost; have ho {F:lots G n}(H: Integrable F (prior G n)):Integrable (fun U=> F U*J U) (prior G n):= H.mul_bdd hp.meas.aestronglyMeasurable (Eventually.of_forall h)
        rw [← sub_zero (πfee E J), ← hm]; unfold πfee γfee; rw[← integral_sub (ho he) (ho hh), ← integral_const_mul]; exact norm_integral_le_of_norm_le ((hp.integrableC _).norm.const_mul _) (Eventually.of_forall fun i=> by rw [←sub_mul,norm_mul]; exact mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _))
noncomputable def Pennant (R:Rep G n)(r:ℕ)(b:ℝ) (S:lots G n): Prop:= ∀ J:lots G n,LocalOn (Push.Mark.Outer r 0) J→Envelope J→‖πfee S J‖ ≤ Real.exp (rhoE R)*b*γfee J
include H
lemma compass (T:Extraction.Lease.Trial C) (Y:Rowe C l)(hm: manifest T r m)(hF:screens C (upper C Y-T) l f)(hp:C.ref l ≤ k)(v:ℕ→ℝ)(hv:∀ i, 0 < v i) : ∀ᶠ i:ℕ×ℕ in f.fuse,∀ he:k ≤ i.1,Pennant (C.path.rep i.1 i.2 k) (fleet C.path k r) (v i.2) ((Owl.Stepm H hp he i.2 (Lake.tallyman H l k i (Y i))).density 0 (C.localSection l) (C.path.rep i.1 i.2 k)):=by -- Trial namespace
        filter_upwards [hF k hp v hv,(Push.RelayDifference.cutoff_grows f).eventually (Push.Mark.lengths C.S m)] with i hi hu he
        obtain ⟨N,p⟩:=i; let x:= Y (N,p); obtain ⟨z,hz,hV,hT⟩:= hm N p; let t:= z ∘ expandAt (0:Site (C.side N p)); have ht: T N p 0=t:=funext (hT 0); let Q:= puff C.path N p l t he; have ha:Continuous t:= Push.Mark.onStencil _ hz
        intro J hJ hr; rw[Ecost H p hp he]; refine costV Q _ _ (puffInt _ ha he _) (puffInt _ (C.continuousO ..) he _) hr (microK C.path z hz hV (hu p) (Overlay.beta_positive H.wilson le_rfl).ne' he l hJ hr) (fun U=>?_)
        specialize hi he U; change ‖puff C.path N p l (C.O N p x 0 - T N p 0) he U‖ ≤ _ at hi; rw [ht, sale _ _ (C.continuousO ..) ha] at hi; exact hi
end YM.OPE.Eyrie
