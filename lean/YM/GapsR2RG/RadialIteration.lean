import YM.GapsR2RG.Directions
/-!
# Affine-null direction charged before full upper-depth transfer
Use `GapsR2RG.Setting` Campaign / same Citizen. Counterterm choice only
for assertion on remainder projections, NOT a PT coefficient routine.
Normalization factor L^4 on each upward-to-downward transfer in `Answers`.
Keep the whole κ-weighted input, all flags in the derivative.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option quotPrecheck false
noncomputable section
namespace YM.GapsR2RG.Anchor
open Lattice Wilson RG RG.Activities PhysicalNext PhysicalNext.JointLoad.Heir
open Labels Source Function Filter Set MeasureTheory Finset Extra.Histories Extra.Histories.Relay MergeProof
open Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open scoped Classical Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G:Gauge}{n:Side}
namespace Legacy
noncomputable def slice (D:Rep G n):Anchor.Stratum G n :=
   ⟨fun i=> if (D.activities.reg i).site=0 then (D.activities.reg i).support else {0},
    fun i=> if (D.activities.reg i).site=0 then D.activities.E i else 0,
    fun i=> if 0∈(D.activities.forced i).support then D.activities.K i else 0⟩
lemma atSlice {δ w s C Λ :ℝ}{D:Rep G n}(h:D.Lawful s C Λ δ w)(hw:0<w): Affidavit D (slice D) (Real.sqrt w) (δ+Real.sqrt w) :=by
   let A:=D.activities; let P:=D.p
   have hr:=h.labels.regular; have hK:=h.labels.forced; have ha:= h.labels.boundE; have hb:=h.labels.boundK; change D.activities.EBound D.p _ at ha; change D.activities.KBound D.p _ at hb
   obtain ⟨e,he,hE⟩:=ha; obtain ⟨k,hk,hj⟩:=hb
   let e' i:= if (D.activities.reg i).site=0 then e i else 0; let k' i:= if 0∈(D.activities.forced i).support then k i else 0; let T:=slice D
   constructor
   · intro i; by_cases he:(D.activities.reg i).site=0
     · change Seed D.p _ _ _; simpa [slice,show (D.activities.reg i).site=0 from he] using (Seed.family hr i)
     simp_rw [slice,if_neg he]; exact ⟨AnalyticBridge.VerifiedReset.reg_const _,Finset.mem_singleton_self _,rfl,fun _ _ _ _ _=>AnalyticBridge.VerifiedReset.hessian_zero ..⟩
   · intro i U h; by_cases ht:0∈(D.activities.forced i).support
     · apply hK.permit; simpa only [slice,if_pos ht] using h
     exact (h (by simp [slice,if_neg ht])).elim
   · intro i hv; by_contra hn; exact hv (by simp [slice,hn])
   · intro i; by_cases ht:0∈(D.activities.forced i).support
     · simpa only [slice,if_pos ht] using hK.sym i
     simp_rw [slice,if_neg ht]; exact fun _ _=>rfl
   · intro i; by_cases ht:0∈(D.activities.forced i).support
     · simpa only [slice,if_pos ht] using hK.reads i
     simp_rw [slice,if_neg ht]; exact fun _ _ _ _=>rfl
   · intro i; by_cases ht:0∈(D.activities.forced i).support
     · simpa only [slice,if_pos ht] using hK.meas i
     simp only [slice,if_neg ht]; exact measurable_const
   refine ⟨δ,Real.sqrt w,le_trans (show 0 ≤ _ from Push.AbsoluteSums.budget_nonneg (hE 0)) le_rfl,Real.sqrt_nonneg _,le_rfl,Real.sqrt_pos.mpr hw,⟨e',?_ ,fun i=> ?_⟩,k',?_,fun i=>?_⟩
   · convert! hE 0 using 1; funext i; by_cases hX:(D.activities.reg i).site=0 <;> simp [e',slice,hX,BudgetPoint.mass]
   · change P.supBounds 0 _ _ _; by_cases hi:(D.activities.reg i).site=0
     · simpa [slice,e',hi] using! (he i)
     simp only [slice,if_neg hi,e']; exact (show |(0:ℝ)|=(0:ℝ) from abs_zero).symm ▸ AnalyticBridge.VerifiedReset.sup_const 0
   · simpa only [show Real.sqrt w * Real.sqrt w = w from Real.mul_self_sqrt hw.le, k',mul_ite,BudgetPoint.mass,mul_zero] using! hj 0
   by_cases hi:0∈(D.activities.forced i).support
   · simpa only [k',slice,if_pos hi] using hk i
   simp [k',slice,if_neg hi]
end Legacy
variable {C:Family G}{W:Bid.Worth}{r:ℕ → ℕ}{D:∀ N p m:ℕ,m<N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
  (hc:C.Makes)(HG:G.Simple)(Y:Citizen C W r D)
local notation "𝒦" i => C.path.levels.clock.forcedAllowance i
local notation "𝓑" => C.path.levels
local notation "F4" => C.labels.level 4
local notation "R4"=> C.localSection 4
local notation "M4"=>Extra.Histories.Music F4 C.path

include hc HG Y
lemma tour (N p:ℕ) (hn:C.ref 4  ≤  N): ∃ M : Extra.Histories.Music (C.labels.level 4) C.path N p,
     Sung R4 C.path N p C.params W (C.ref 4) M ∧ (C.factory 4 N p).entries=(M.draft C.path).inits ∧
     ∀ l m:ℕ, C.ref 4  ≤  l →  l ≤ m  →  m ≤ N  →  ∀ (Z:Anchor.Stratum G (C.side m p))(t:ℝ), Affidavit (C.path.rep N p m) Z (Real.sqrt (𝒦 m)) t  → 
     ∃ Q : ∀ i, Solo F4 C.path p i, Q m=pair C.path N p M (sheath F4 Z) t ∧ Challenge R4 C.path N p C.params W M l m Q ∧
      (∀ v, ((Q m).bar M v).x=(M.tone m).index v ∧
       ((Q m).bar M v).density 0 R4 (C.path.rep N p m) = responseAt (C.path.rep N p m) Z +
        ((M.tone m).plays v).density 0 R4 (C.path.rep N p m)) ∧
      let P:= dualize C.path N p M l m Q (-(Q l).a)
      ((Q l).bar M 0).x=(M.tone l).index (Q l).a ∧ P.Woke C.params W R4 t ∧ ∀ i, l ≤ i → i ≤ m  → 
        Bid.gainChart C.path m i*(P.cost i+(F4).coeffSize (P.voice i).x)  ≤  4*(1+((𝓑).params m).columns)*t := by
  obtain ⟨M,hV,hS,hC,hY⟩:= (Y.system.costs.aim 4 N p hn).lyrics
  refine ⟨M,hS,hV,fun l m hl hM hk Z t ht=>?_⟩
  have hb : 4  ≤  (C.side m p).val:= by have h₁:= (𝓑).fits.sizeT m p; change _  ≤  (C.side m p).val at h₁; omega
  obtain ⟨hZ,H⟩:=contractS (C.labels.level 4) C.params Z ht HG hb
  obtain ⟨Q,hQ,hv,h₁,h₂,h₃,h₄,h₅⟩:= Relay.antilles R4 C.path N p C.params W M (D N p) _ hl hM hk hc.wilson hS (fun i hi hm=>⟨Y.system.listens _ N p i (hl.trans hi) (hm.trans_le hk),hC i (hl.trans hi) (hm.trans_le hk)⟩) (sheath F4 Z) hZ H (fees F4 C.params Z ht HG hb) Y.system.costs.cost Y.system.costs.back
  exact ⟨Q,hQ,hv,fun v=>⟨((h₂ v).1.trans (zero_add _)),(h₂ v).2.trans (congr_arg₂ _ (recognized F4 Z R4) rfl)⟩,h₃,h₄,h₅⟩

/-- Price of one-step perturbation in any intermediate law at aligned origin, with exact incumbent D denominator (derivative not a primary normalization). -/
lemma stepwise {m N p:ℕ}(hm:m+1 ≤ N)(hl:C.ref 4 ≤ m)
    (Z:Anchor.Stratum G (C.side (m+1) p))(t:ℝ)(ht: Affidavit (C.path.rep N p (m+1)) Z (Real.sqrt (C.path.levels.clock.forcedAllowance (m+1))) t) : ∃ U:Coefficient (C.labels.level 4) (C.side m p),
      let Q:= C.path.rep N p m
      U.density 0 R4 Q = blast C.path N p m 4 (responseAt (C.path.rep N p (m+1)) Z) ∧ U.Format 0 C.params Q ∧
          U.remBound 0 Q (Real.sqrt (𝒦 m)) (Bid.barunit (C.S.block m)*t) ∧ (F4).coeffSize U.x  ≤  Bid.barunit (C.S.block m)*t :=by
  obtain ⟨η,hZ⟩:=Y.system.listens _ N p m hl hm; obtain ⟨hk,_,_,hr⟩:= hZ.tuned
  let c:=(𝓑).params m |>.columns
  have hy:η  ≤  Bid.barunit (C.S.block m) := (le_mul_of_one_le_left hr (show 1 ≤ 1+2*c by have hp:= ((𝓑).params m).columns_ge; linarith)).trans hk
  let F':= sheath (C.labels.level 4) Z
  obtain ⟨W',hW,h'⟩:= hZ.priced
  obtain ⟨hF,H⟩:=contractS (C.labels.level 4) C.params Z ht HG ((by have h₁:= (𝓑).fits.sizeT (m+1) p; change _  ≤  (C.side (m+1) p).val at h₁; omega))
  obtain ⟨U,hU,ha⟩:= h' F' t rfl hF H
  have hq : 0 ≤ t := by obtain ⟨a,b,ha,hb,h,_⟩:=ht.budget; linarith only [ha,hb,h]
  refine ⟨U,hU.agrees.trans (congr_arg _ (recognized _ _ _)),hU.format,?_ ,?_⟩
  · unfold Coefficient.remBound
    obtain ⟨a,b,ha,hb,he,hk,hR,hZ⟩:=hU.bound
    exact ⟨a,b,ha,hb,he.trans (mul_le_mul_of_nonneg_right hy hq),hk,hR,hZ⟩
  exact ((le_mul_of_one_le_left (Work.G08.size_nonneg ..) (Extra.Histories.Motion.orbitCost_one_le (F4))).trans (sub_zero (U.x) ▸ hU.leadP)).trans (mul_le_mul_of_nonneg_right hy hq)
-- update price field use Actual fees
end YM.GapsR2RG.Anchor
