import YM.MergeProof.Canyon
import YM.OPE.Compatible.Eyrie.Aurora
/-! # Suns under linear growth. All period errors in `.fuse`, arbitrarily fast along p only after horizon/family. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels OPE.Eyrie
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels)
variable {f:Extraction.Order}{N p k d:ℕ}(V:SectionData (C.labels.level d))(hV:V.Sound C.params)
    {ζ:ℕ→ℕ→ℝ}{E:ℕ→ℝ}{P:ℕ→ℕ→(C.label d≃ₗ[ℂ] C.label d)}{U:ℕ→ℕ→(C.labels.level d).Index→ C.label d}
    (h:Hearth V ζ E P U) (h': Sun V E U)
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "Φ"=> C.path
local notation "s'"=> (Size.axis (C.labels.level d))
local notation "ρ"=> Motion.Tally (C.labels.level d)
section
variable {D:ℕ→ℝ}
lemma faresSlow : Slow C f fun j=> D j.2:=by
        intro ε he; rw [Order.fused]
        unfold Order.late; refine Eventually.of_forall fun i=> ?_; exact (Real.tendsto_exp_atTop.comp ((C.S.divergent.comp f.mesh.cofinal).const_mul_atTop he)).eventually_ge_atTop ‖D (f.per i)‖
lemma taxi (B:ℕ→ℝ)(x:ℕ × ℕ→ℝ)(ht:Slow C f x)(k:ℕ) (he:∀ i:ℕ,0<D i) : ∀ᶠ i:ℕ×ℕ in f.fuse,B i.2*x i/gainChart C.path i.1 k ≤ D i.2:=by
        let w:=Real.exp ((1/8:ℝ)*C.S.scale k); let z (i: Cutoffs):= (D i.2)⁻¹*(B i.2*x i)*w; have hz : Slow C f z:= ((faresSlow (D:=fun i=>(D i)⁻¹)).mul ((faresSlow (D:=B)).mul ht)).mul (Slow.const _)
        have hT:= hz.sink (show (1/16:ℝ)<1/8 by norm_num); filter_upwards [hT, (flight_lands (C:=C) (ε:=1/16) (by norm_num)).eventually (ge_mem_nhds (show (0:ℝ)<1 from by norm_num))] with i hi hk
        have hv : z i * flight C (-(1/8)) i = (D i.2)⁻¹*(B i.2*x i/gainChart C.path i.1 k):=by unfold z w gainChart flight Family.S; rw [mul_sub,Real.exp_sub,neg_mul,Real.exp_neg]; ring_nf; simp only [inv_inv]; ring
        apply le_of_mul_le_mul_left _ (inv_pos.mpr (he i.2)); rw [← hv]; exact (hi.trans hk).trans_eq (inv_mul_cancel₀ (he i.2).ne'|>.symm)
lemma balloons {J:Type} (d:ℕ)(s:Finset J)(X:J→lots G (C.side N p))(hp:∀ i,Continuous (X i))(hk:k≤N): OPE.Eyrie.puff Φ N p d (∑ i∈s,X i) hk=∑ i∈s, OPE.Eyrie.puff Φ N p d (X i) hk:=by
        induction s using Finset.induction_on with
        | empty=> rw[Finset.sum_empty,Finset.sum_empty]; let v:lots G (C.side N p):= 0; rw [← zero_smul ℂ (0:lots G (C.side N p)), Opal C.path hk v (show Continuous v from continuous_const)]; rw [zero_smul]
        | insert i s hi ih=> simp only [Finset.sum_insert hi]; have he:Continuous (∑ i∈s,X i):=by rw [funext (fun x=> Finset.sum_apply (M:=fun _=>ℂ) x s X)]; exact continuous_finsetSum _ (fun i _=> hp i)
                             rw[WaveF C.path hk (X i) _ (hp i) he,ih]
lemma decor_eqQ (A: Frame G d)(w:A.Coeff)(f:A.Index→A.Coeff): decor A f w=repaint A f w:=by
    exact decor_apply_eq_repaint A f w
end
end YM.MergeProof
