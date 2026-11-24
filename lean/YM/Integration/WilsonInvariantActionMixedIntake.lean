import YM.Integration.WilsonRegisteredIntakeSeats
import YM.Integration.WilsonCoherentMayerSlots
import YM.Integration.WilsonInvariantActionMixedMaterial

/-! File the two measured legs of the primary/previous contribution on the
same inherited Q carrier, with the literal physical masks at every field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionMixedIntake
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical


open AnalyticBridge.VerifiedReset WilsonCoherentMayerSubmission
open WilsonInvariantActionMixedMaterial

open PhysicalNext.Repeat.Legato WilsonInheritedRegisteredField
variable {G:Gauge} (R:Run G)


private theorem real_factor {k d:ℕ} (η:ℂ→L[ℝ]ℝ) (z:ℂ):
    η (MergeProof.alto R.family.path k d*z)=(R.family.S.a k^d)⁻¹*η z:=by
  simpa only [MergeProof.alto,Complex.real_smul,smul_eq_mul,Complex.ofReal_inv,Complex.ofReal_pow]
    using η.map_smul ((R.family.S.a k^d)⁻¹) z

theorem original {k N per f p:ℕ} {t:ℝ} (live:k≤N) (ref:R.family.ref 4≤k)
    (onset:R.family.ref (max f p)≤k) (Q:Rep G (R.family.side k per))
    (record:LocalComparison.NormAt R.family k Q.p f p t) (v w:R.family.label 4) (x y:Site (R.family.side k per)):
    let P:=R.family.path.rep N per k
    let X:=packet R.makes live v x;let Z:=packet R.makes live w y
    let L:=R.family.labels.level 4;let S:=R.family.localSection 4
    let Y:=QLocalInheritedRegularSlots.carrier Q;let α:ℝ:=(R.family.S.a k^4)⁻¹
    let cap:=(R.family.path.levels.params k).columns*L.coeffSize (L.core Z.x)
    ∃e:ℕ→ℝ, SumBudget (fun i=>P.p.mass (Z.support i) (e i)) cap ∧
      (t≤P.p.supportExponent→SumBudget (fun i=>Q.p.mass (Z.support i) (e i)) cap) ∧
      ∀(i:ℕ)(η χ:ℂ→L[ℝ]ℝ), (∀z,|χ z|≤‖z‖) → ∀old:Team Y,
        ∃(W:Team Y) (a b:Leaf Y), W.own=insert a (insert b old.own) ∧
          a∉insert b old.own ∧ b∉old.own ∧ a.crest=S.footprint x ∧ b.crest=Z.support i ∧
          W.weight=WilsonCoherentMayerEntry.wallet R (L.core X.x) P.p.threshold η*(old.weight*e i) ∧
          ∀U,α*a.ingredient U=η (primary R.makes live v x U) ∧
            α*b.ingredient U=χ (earlier R.makes live w y ({i}:Set ℕ) U) ∧
            α^2*(∏l∈W.own,l.ingredient U)=
              (η (primary R.makes live v x U)*χ (earlier R.makes live w y ({i}:Set ℕ) U))*
                ∏l∈old.own,l.ingredient U:=by
  intro P X Z L S Y α cap
  obtain ⟨e,bill,rebill,_,buy⟩:=WilsonRegisteredIntakeSeats.issued R live ref onset Q record w y
  refine ⟨e,bill,rebill,?_⟩
  intro i η χ contract old
  obtain ⟨J,b,joined,new,amount,scope,read⟩:=buy i χ contract old
  let grades:=fun _:Fin 1=>(4:ℕ);let sites:=fun _:Fin 1=>x
  let labels:=fun _:Fin 1=>L.core X.x;let phases:=fun _:Fin 1=>η
  let shelf:=WilsonCoherentMayerSlots.inherited Q
  let s:=WilsonCoherentMayerSlots.issued R grades sites J shelf labels phases
  let a:=row s 0
  have fresh:=WilsonCoherentMayerSlots.fresh R grades sites J shelf labels phases
  let W:=together s J fresh
  have unoccupied:a∉J.own:=fun h=>fresh a h 0 rfl
  have single:occupied s={a}:=by
    unfold occupied
    rw [Finset.univ_unique,Finset.image_singleton]
    rfl
  have enrolled:W.own=insert a J.own:=by
    change J.own∪occupied s=_
    rw [single,Finset.union_singleton]
  have weight:W.weight=a.weight*J.weight:=by
    change (∏l∈W.own,l.weight)=a.weight*∏l∈J.own,l.weight
    rw [enrolled,Finset.prod_insert unoccupied]
  have same:Y.p.threshold=P.p.threshold:=(WilsonRegisteredIntakeNorm.dated R live onset Q.p record).1
  have crest:(Y.activities.reg (s.key 0)).support=S.footprint x:=by
    change (Y.activities.reg (WilsonCoherentMayerSlots.key R grades sites J 0)).support=_
    unfold WilsonCoherentMayerSlots.key
    rw [(shelf _ _).1]
    rfl
  have fee:a.weight=WilsonCoherentMayerEntry.wallet R (L.core X.x) P.p.threshold η:=by
    change WilsonCoherentMayerEntry.wallet R (L.core X.x) Y.p.threshold η=_
    rw [same]
  refine ⟨W,a,b,enrolled.trans (congrArg (insert a) joined),joined ▸ unoccupied,new,crest,scope,?_,?_⟩
  · rw [weight,fee,amount]
  · intro U
    let spot:=S.footprint x
    let raw:=S.places (L.scaled P.p.threshold⁻¹ (L.core X.x)) x
    have planted:a.ingredient U=η (masked P.p.threshold spot raw U):=by
      change masked Y.p.threshold (Y.activities.reg (s.key 0)).support
        (fun V=>η (S.places (L.scaled Y.p.threshold⁻¹ (L.core X.x)) x V)) U=_
      rw [same,crest]
      by_cases clean:Healthy P.p.threshold spot U
      · exact (masked_eq _ _ _ _ clean).trans (congrArg η (masked_eq _ _ _ _ clean).symm)
      · rw [masked_ne _ _ _ _ clean,masked_ne _ _ _ _ clean,map_zero]
    have first:α*a.ingredient U=η (primary R.makes live v x U):=by
      rw [planted]
      exact (real_factor R η (masked P.p.threshold spot raw U)).symm
    have second:α*b.ingredient U=χ (earlier R.makes live w y ({i}:Set ℕ) U):=by
      rw [read U]
      have one:earlier R.makes live w y ({i}:Set ℕ) U=MergeProof.alto R.family.path k 4*Z.maskedTerm P i U:=by
        simp only [earlier,Set.mem_singleton_iff,tsum_ite_eq, Z,P]
        rfl
      rw [one]
      exact (real_factor R χ (Z.maskedTerm P i U)).symm
    refine ⟨first,second,?_⟩
    rw [enrolled,Finset.prod_insert unoccupied,joined,Finset.prod_insert new,←first,←second]
    ring

end YM.Integration.WilsonInvariantActionMixedIntake
