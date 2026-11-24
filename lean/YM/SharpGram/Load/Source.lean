import YM.Pert.FirstTarget
import YM.SharpGram.Lenses.Sights

/-!
# Install a genuine Supplier on every focus

The frozen witness supplies probe leading on exactly its own trajectory and
through entire ranges of plaque. To make comparisons in **fixed** physical
coords, one generally needs more than the leading term: the quantitative source
read-out matters. There is nonetheless a positive all-k-quoted sector
(not only units) where it is enough. Use Ward and actual normalization. In
preparing this, reduce to the Supplier on an unknown subsequence of arbitrary
challenging scale paths in the Mantle. Problems across other subseqs won't be
discarded; leading roll-ins done on all k by a separate argument later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Ward Org Extraction Analysis Spec Next.UVStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} (F:Final C f S)
local notation "σ" => F.room.kernel.spin
local notation "E" => F.sector.energy
local notation "V" => F.sector.derivatives
local notation "S'"=> (Bel C.book)
local notation "α"=> F.sector.turns.lie
local notation "T" => F.phase.transport
local notation "H" => F.room.kernel
variable {M:MaxwellData C}

lemma chosen_lit (hG:G.Simple) :
    ∃ M : MaxwellData C, M.T.W = Maxwell.Free.scheme C.labels ∧ M.T.K = Maxwell.Free.gear C.labels ∧
      M.T.J = YM.UVNext.FreeStress.torch C.book.grid 1 ∧ Tensorial M.T.K M.T.J ∧ FreeDiv M.T M.hT M.lit.hers := by
  obtain ⟨T1,hM,_⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
  obtain ⟨M,hJ,hm,hk,_,_,ht,hd⟩:= YM.UVNext.FreeStress.fire hG T1 1 one_ne_zero
  exact ⟨M, hm.trans (congr_arg Lighthouse.W hM), hk.trans (congr_arg Lighthouse.K hM),hJ, hk.symm ▸ ht, hd⟩

-- An *interpreted* Ward tensor, no choice beyond Final witness.
def baser (b:ℝ) : IR (C:=C) S := ⟨b • reCenter S E,b • (V).deriv,b • α⟩

lemma true_tensor : RawTensor σ E := by
   intro i a b; rw [← (T).spots.signed]; exact (T).spin ..

def centeredK : KernelSpace σ := ⟨reCenter S E, enters H _
     (sym_mem.mpr ⟨(T).conserved.symmetric,(T).conserved.real,true_tensor F⟩)⟩

lemma centered_charge : StressLaws S (reCenter S E) (V).deriv α := by
  let down (i j:Axis) := -expectation S 4 (E i j)
  rw [show reCenter S E = E + UVNext.FreeStress.fossil down from ?_]
  exact UVNext.FreeStress.add_unit H (T).charges _ fun i j => by dsimp only [down]; rw [(T).conserved.symmetric]
  funext i j
  change centering S 4 (E i j) = E i j + down i j • S.unit 4
  rw [value_center]; simp [down,sub_eq_add_neg]
lemma centered_div : currentDiv V σ (T).rights (centeredK F) = 0 := by
  apply (linear_cons ..).2
  obtain ⟨e1,e2,e3⟩ := sym_mem.mp (kernel_mem.mp (centeredK F).property).1
  refine ⟨e1,e2,fun j => ?_⟩
  change ∑ a, (V).deriv 4 a (centering S 4 _) = 0
  have hd := (V).unit_drop (H).laws (T).derivatives (H).smooth 4
  simp_rw [value_center,map_sub,map_smul,hd,smul_zero,sub_zero,(T).conserved.divergence]

lemma starts_ready (b:ℝ) : Pre H V (baser F b).J (baser F b).p (baser F b).Y := by
  let k := b • centeredK F
  refine ⟨?_, (sym_mem.mp (kernel_mem.mp k.property).1).2.2, ?_⟩
  · apply (linear_cons _ _ (T).rights k).1; rw [show k=b • centeredK F from rfl, map_smul, centered_div,smul_zero]
  exact UVNext.FreeStress.scale_stress H (centered_charge F) b

variable (X : Scaling S) (hx : Approaches (path X) (isoPanel X)) (hS : Stable F.room.kernel.spin M.hT.spin F.sector.derivatives M.T.W X)
include F hx
lemma delivered (d : ℕ) : Bid.ConLap X (V).deriv d M.T.W.deriv X.r := by
  unfold Bid.ConLap
  refine tendsto_pi_nhds.mpr fun a=>?_
  have he := bend_limit H (T).derivatives M.hT M.lit.pales X d a hx
  exact he

lemma centered_lit (M : MaxwellData C) : reCenter S E ≠ 0 := by
    apply Extra.WeakScaling.flux_nontrivial H _ (centered_charge F)
    intro h
    have ht : leaves (V).deriv 4=0 := by rw [h];rfl
    have hT := delivered (M:=M) F X hx 4
    unfold Bid.ConLap at hT; rw [ht] at hT
    apply M.lit.born
    apply tendsto_nhds_unique hT
    refine tendsto_const_nhds.congr ?_; intro k; rw [map_zero]; exact (funext fun j => ContinuousLinearMap.ext (fun v => (show X.r k • ((0 : (Bel C.book).Field 4 →L[ℂ] (Bel C.book).Field (4+1)) v)=0 from smul_zero _))).symm

include hS
lemma meterFrom (hDiv:FreeDiv M.T M.hT M.lit.hers) : ∃ (s:Sequence) (t:ℕ→ℝ) (ht:∀ i,0<t i) (c:ℝ),
    c≠0 ∧ (narrow X s t ht).meter (baser F c).J M.T.J := by
  let a:=centeredK F; have ha : a.val≠0:=centered_lit F X hx M
  obtain ⟨s,R,hr,Hr⟩ := subsector X a.val M.T.J ha hDiv.sign
  let Y := narrow X s _ (fun k => positive_strength X (s k) ha hDiv.sign)
  have hY := narrow_path X s _ (fun k => positive_strength X (s k) ha hDiv.sign) hx
  have hS := narrow_stable X s _ (fun k => positive_strength X (s k) ha hDiv.sign) hS
  obtain ⟨v,hv,hF⟩ := on_axis Y H (T).derivatives (T).rights a (centered_div F) M.hT M.lit.pales M.lit.hers hY hS R Hr
  let t : KernelSpace M.hT.spin := ⟨M.T.J,hDiv.enters⟩
  let j : LinearMap.ker (currentDiv M.T.W M.hT.spin M.lit.hers) := ⟨t, (linear_cons _ _ M.lit.hers t).2 hDiv.origin⟩
  have e : j ≠ 0 := fun e=> hDiv.sign (congr_arg (fun (x : LinearMap.ker (currentDiv M.T.W M.hT.spin M.lit.hers)) => x.val.val) e)
  obtain ⟨c,hc⟩ := (finrank_eq_one_iff_of_nonzero' j e).1 hDiv.one ⟨v,hF⟩
  have hc : c • M.T.J = R := (congr_arg (fun (x : LinearMap.ker (currentDiv M.T.W M.hT.spin M.lit.hers)) => x.val.val) hc).trans hv
  have hz : c ≠ 0 := by
     intro h; exact (norm_ne_zero_iff.mpr hDiv.sign) (by rw [← hr, ← hc, h, zero_smul, norm_zero])
  refine ⟨s,Y.xi,Y.sign,c⁻¹,inv_ne_zero hz,?_⟩
  intro i j
  have hh : Tendsto (fun k=> c⁻¹ • balanced_J Y a.val k) atTop (𝓝 M.T.J):=by
    rw [show M.T.J=c⁻¹ • R from by rw [← hc,inv_smul_smul₀ hz]]
    exact (tendsto_const_nhds.smul Hr)
  refine (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hh i) j).congr fun k=>?_
  change c⁻¹ • balanced_J Y a.val k i j=(Y.U k 4).symm ((_:ℂ) • (c⁻¹ • a.val i j))
  apply (Y.U k 4).injective
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) c⁻¹,map_smul,balanced_value,LinearEquiv.apply_symm_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ) c⁻¹]
  exact smul_comm ..

include hS
/-- Don't use new existential plane across meters. Feeds the existing
physical Supplier **for a subsequence** of an arbitrary compatible scaling,
uses real Graded and actual (H). UV includes Grill from Facilities. IR here is
rescaled existing Ward normalization. -/
theorem reach (hg : Org.Grill C f) (hDiv: FreeDiv M.T M.hT M.lit.hers) :
    ∃ (s:Sequence)(t:ℕ→ℝ)(ht:∀ i,0<t i)(c:ℝ), c≠0 ∧
       Pert.Supplier f V M (baser F c) (narrow X s t ht) := by
   obtain ⟨s,t,ht,c,hc,hV⟩ := meterFrom F X hx hS hDiv
   let Y:=narrow X s t ht
   let I:= baser F c
   have hF := narrow_path X s _ ht hx
   have hG := narrow_stable X s t ht hS
   exact ⟨s,t,ht,c,hc,⟨F.room,(T).rights,starts_ready F c,
     focused H (T).derivatives M.hT M.T M.lit.pales Y hF hG I.J hV,hg⟩,(T).injection,(T).derivatives,
     smul_ne_zero hc (centered_lit F X hx M),(c • centeredK F).property,hDiv,hF,hG,hV⟩
end YM.SharpGram.Load
