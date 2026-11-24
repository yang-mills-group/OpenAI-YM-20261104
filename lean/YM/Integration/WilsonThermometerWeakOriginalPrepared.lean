import YM.Integration.WilsonThermometerWeakOriginalCopyPrices
import YM.Integration.WilsonThermometerWeakOriginalHardCopy

/-! The receiving Wilson weak course, for distinct displaced programs replicated through
one physical measure. The entire signed source and the original quiet divisor are reissued
on the bridged representation with its indicated regular and forced prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakOriginalPrepared
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Next.Rank Next.Rank.Edition Next.Rank.Spindle Configuration Rise
open Thirst Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential
open WilsonThermometerWeakOriginalReclosure
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V ι κ:Type} [Fintype V] [DecidableEq V] [Fintype ι] [Fintype κ]
variable {d:V→ℕ} {F:(x:V)→Frame G (d x)} {η:Hol G} {P Q:Rep G n} {ζ:V→Site n}

theorem delivered (T:(i:V)→SectionData (F i)) (X:(i:V)→ Coefficient (F i) n)
    (form:∀ i,(X i).Format 0 η P) (s:V→Signed) (a:V→Prop) (vac:Neat n→Burst G n P.p.threshold)
    (L:κ→Lifted G ζ P.p.threshold) (A:ι→SourceAt G ζ)
    (file error:V→SourceAt G ζ) (forced:V→Strike G ζ Q.p.threshold) (far:V→Keepat n→SourceAt G ζ)
    (Z:Support n) (i:ℕ) {r w e z β σ Λ d' c' δ w' γ u:ℝ}
    (low:Lower P.p Q.p) (sep:Spaced P.p.B ζ) (hu:0<w) (hz:0≤z) (he:0≤e) (hr:0<r) (hy:0≤w') (hs:0≤d')
    (rebate:BudgetMix P.p Q.p r w (e+2) γ) (scale:scalesExp P.p Q.p (2*(e+2)))
    (sig:Siren G n Q.p.threshold) (W:ValidX n→Wickless G n Q.p.threshold) (b:Bridges P Q e z σ β Λ δ sig W (q:=Q.p))
    (vacuum:IsoVac P vac u) (cash:V→ℝ) (budget:∀ j,(X j).remBound 0 P (Real.sqrt u) (cash j)) (money:∀ j,w*cash j≤w')
    (regular:Unpacks A P.p (fun _=>r) P.p.supportExponent 1) (hard:Unfold (p:=P.p) L (fun _=>r) P.p.supportExponent 1)
    (reg2:∀ j,2≤(A j).fires.val.card) (hard2:∀ j,2≤(L j).fires.val.card)
    (xe:∀ j,(error j).extent=swath (s j) (ζ j) Z) (fe:∀ j,(error j).fires=slot j)
    (xf:∀ j,(forced j).extent=halo 8 (swath (s j) (ζ j) Z)) (ff:∀ j,(forced j).fires=slot j)
    (farSlot:∀ j h,(far j h).fires=slot j)
    (emit:∀ j U,Poly.send (slot j) (dot (a j) ((X j).exponentialEntry 0 (T j) P (pull (s j) (ζ j) U)))=
      (file j).amount Q.p.threshold U+(error j).amount Q.p.threshold U+(forced j).occ U+∑ h,(far j h).amount P.p.threshold U)
    (fees:∀ j,transported (error j) Q.p.threshold (fun _=>w) c')
    (caps:∀ j,Taxed (forced j) (q:=Q.p) (fun _=>w) (3*w'))
    (farFees:∀ j,∃c:Keepat n→ℝ,
      (∀ h,transported (far j h) P.p.threshold (fun _=>w) (c h)) ∧
      (∑ h,c h*debt Q.p.B (e+2) (halo 8 (far j h).extent))≤
        Real.exp (100000*(e+2))*Real.exp (-(P.p.supportExponent*i)/2)*w')
    (total:2*vacancies e Λ σ β δ P.beta P.p Q.p+strand Z i P.p Q.p w' e γ+
      mech u Q.p w' e γ+batch z (e+1) Q.p.B≤d') (size:(↑((Q.p.B+Q.p.B+1)^4:ℕ):ℝ)*d'≤1):
    let Y:=teat (elders X form s a vac L) (Sum.elim (fun j=>(W j).credit ζ) (strikes A forced far low.good)) sig
    credsX ζ T X form s a vac (fun _=>1) L A=dust Q (entries A file error far) Y ∧ Background Q Y ∧
    Unpacks (Sum.elim error (carry A far)) Q.p (fun _=>w) e (c'*debt Q.p.B e Z+drain i P.p Q.p w' e γ) ∧
    Alarm.prepared (q:=Q.p) Y (fun _=>w) e (Real.exp (-z)*(Real.exp d'-1)) := by
  let rW:V→ℝ:=fun _=>w
  let U:=drain i P.p Q.p w' e γ
  have U0:0≤U:=by unfold U drain;positivity
  have eq:(e+1)+1=e+2:=by ring
  have esp:scalesExp P.p Q.p (e+1+1):=by apply le_trans _ scale;gcongr;linarith only [he]
  have inj:=injected P.p.B ζ P.p.B_pos sep
  have branches:=fun e':ℝ=>WilsonThermometerWeakOriginalCopyPrices.short Q.p e' rW error forced inj xe fe xf ff fees caps
    (fun _=>le_rfl) (fun _=>le_rfl) (mul_nonneg (by norm_num) hy)
  choose c h pay using farFees
  have packed:=WilsonThermometerWeakOriginalCopyPrices.wide P.p Q.p rW (e+2) _ far h pay farSlot
  have cover:Credit (carry A far) P.p Q.p rW (e+2) U:=by
    apply Credit.relax (Credit.mix (transfer _ regular reg2 rebate hr hu sep) packed);unfold U drain;simp
  have failed:taxable (q:=Q.p) (strikes A forced far low.good) rW (e+1) (strand Z i P.p Q.p w' e γ):=by
    have booked:=dash_credit P.p Q.p (show Credit (carry A far) P.p Q.p rW (e+1+1) U from eq.symm ▸ cover) low.good inj U0
    apply Edition.taxable.relax (Edition.taxable.add (branches (e+1)).2 booked)
    rw [eq];exact le_rfl
  have old:Burden (elders X form s a vac L) Q.p rW (e+1) (mech u Q.p w' e γ):=by
    have head:=WilsonThermometerWeakOriginalHardCopy.original X form s a vac u vacuum cash budget Q.p rW
      (fun _=>hu.le) hy (add_nonneg he zero_le_one) money low sep esp
    have tail:=rooted_interest hard hard2 (show BudgetMix P.p Q.p r w (e+1+1) γ from eq.symm ▸ rebate)
      hr hu (add_nonneg he zero_le_one) zero_le_one sep
    apply Edition.Burden.up Q.p (sum_token _ _ _ head tail);rw [eq];exact le_rfl
  refine ⟨WilsonThermometerWeakOriginalReclosure.original T X form s a vac L A file error forced far low.good sig W b.predicts ff emit,?_,
    Unpacks.mix (branches e).1 (Credit.spill rW cover low.good (by linarith only) he),?_⟩
  · let K:=elders X form s a vac L
    let B:=Sum.elim (fun i=>(W i).credit ζ) (strikes A forced far low.good)
    have germs:Germs vac W K B:=by
      refine ⟨⟨fun j=>.inl (.inl j),fun x y h=>Sum.inl.inj (Sum.inl.inj h)⟩,
        ⟨.inl,fun _ _ h=>Sum.inl.inj h⟩,fun _=>rfl,fun _=>rfl,?_,?_⟩
      · rintro ((j|j)|j) hj
        · exact ⟨j,rfl⟩
        · have key:slot j.1=quiet V:=hj
          exact (Finset.not_nonempty_empty (show (quiet V).val.Nonempty from key ▸ Finset.singleton_nonempty _)).elim
        have few:=hard2 j;change (L j).fires=quiet V at hj; rw [hj] at few;change 2≤(∅:Finset V).card at few;simp at few
      rintro (j|j) hj
      · exact ⟨j,rfl⟩
      have live:(strikes A forced far low.good j).fires.val.Nonempty:=by
        cases j with
        | inl t=>change (forced t).fires.val.Nonempty;rw [ff];exact Finset.singleton_nonempty _
        | inr t=>exact (carry A far t).chosen
      change (strikes A forced far low.good j).fires=quiet V at hj
      rw [hj] at live; exact (Finset.not_nonempty_empty live).elim
    exact fun j W'=> (Germs.background sig germs j W').trans (b.jacket vac vacuum.points vacuum.value j W')
  exact Alarm.rarity _ _ sig (fun _=>hu) (Edition.taxable.add (Alarm.salary _ b.remain rW) failed)
    old b.head size total he hz hs

end YM.Integration.WilsonThermometerWeakOriginalPrepared
end
