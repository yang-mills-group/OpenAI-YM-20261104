import YM.OPE.Compatible.Yolk.Clip
/-!
# Relative sharp W. Positive vacuum only allgood.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
def film (F:Forest S.ratio)(i:F.Free)(U:Config G f)(b : ℝ):ℝ:=if b<G.chord (pantone F U i.val) then 1 else 0
lemma movie (F:Forest S.ratio)(i:F.Free)(b : ℝ):Paced R (walksAt F i.val) S (fun U=> film F i U b) 1:=by
   refine ⟨?_,?_,?_,?_⟩
   · intro U V h _; have he:G.chord (pantone F U i.val)=G.chord (pantone F V i.val):=congr_arg _ (poses F i.val U V h); change (if _ <G.chord _ then _ else _)=_; rw [he]; rfl
   · have ht : Continuous fun U:Config G f=> G.chord (pantone F U i.val):=by unfold pantone Lattice.gauge; fun_prop
     exact Measurable.ite (measurableSet_lt measurable_const ht.measurable) measurable_const measurable_const
   · intro k h U; have hz:=pantone_in F k h U; change (if _ then _ else _)=(if _ then _ else _); rw [hz]
   · intro U; unfold film; split <;> norm_num
section
variable {K:Keeper R.p R.activities}{b d e v C₀ a' b' σ₀:ℝ}{V:Config G c}
 (hK: S.IsKernel R.beta G) (hR:R.Lawful σ C₀ Λ E w)(ht:HasSlots R.p R.activities) (F : Forest S.ratio) (i:F.Free)
 (hb:Besotted R S a b V w)
 (hx : ∀ M:Leaf S R, (∀ y:F.Slice G,M.ingredient (F.drape y)≠0→ a' < G.chord (y i)) → ‖S.push R.beta M.cicada V‖ ≤ S.push R.beta R.eval V* (d*Real.exp (a*coverNumber R.p.B M.crest)*M.weight))
 (hE : 0≤ d)(hd:0≤a)(hy:0≤w)(hu:0≤b)(hg:0≤S.push R.beta R.eval V)
include hK hR ht hb hx
lemma overtakes : let J:=walksAt F i.val;let z:=S.push R.beta R.eval V
  ‖S.push R.beta (fun U:Config G f => R.eval U*film F i U a') V‖ ≤ z *
   (Real.exp (a*coverNumber R.p.B J)*(d+(Real.exp (J.card*w)-1)*b)):=by
   intro J z; have hh:= movie (R:=R) F i a'; have hJ:J.Nonempty:=⟨_,(costPose F i.val).1⟩
   obtain ⟨M,k,hk,hM,hV,hW⟩:=masking ht hh hJ
   let f(U : Config G f):=film F i U a'; let u:= fun U=> if Healthy R.p.threshold J U then 0 else f U; have hs:=stepped hh
   have hz:(fun U=>R.eval U*f U)=M.cicada + (fun U=>R.eval U*u U):=by
      funext U; rw [Pi.add_apply,M.harmless hk,hV]; unfold u; by_cases hg:Healthy R.p.threshold J U
      · rw [masked_eq _ _ _ _ hg,if_pos hg,mul_zero,add_zero]
      rw [masked_ne _ _ _ _ hg,if_neg hg,mul_zero,zero_add]
   have hv := hb J J le_rfl hJ u 1 hs
   have he i :(fun U=>smudge R J U*u U) i=R.eval i * u i:=by
      by_cases hu:Healthy R.p.threshold J i; · change smudge R J i*u i = _; unfold u; rw [if_pos hu,mul_zero,mul_zero]
      exact congr_arg (·*_) (smolder i hu).symm
   rw [funext he] at hv
   have hG:=hx M fun y hy=> by
      rw [hV] at hy; by_cases ha : a'<G.chord (y i); · exact ha
      apply False.elim; apply hy
      unfold masked Set.indicator; split
      · unfold film; dsimp only; rw [pantone_self,F.off_tree,if_neg ha]
      rfl
   rw [show (fun U=>R.eval U*film F i U a')=_ from hz, StepData.push_add hK _ _ ((M.sells hR).1.integrable _) (((R.envelope hR).mul (Paced.env hs)).integrable _),Pi.add_apply]; apply (norm_add_le ..).trans
   rw [hW,hM] at hG; exact (add_le_add hG hv).trans_eq (by unfold z J; ring)
end
end YM.PhysicalNext.Repeat.Aroma
