import YM.RemainderComparison.Fallow.Currency
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Fallow
open Function Filter Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker Finset
open Solos Mosaic Verse Serif Flues WickReps Ethereal Jolt Lacuna Lobby Passion GridRenewal.Rain PhysicalNext.Repeat WardBin.Crest
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {α:Type*}{G:Gauge}{n:Side}{I:Type}
variable {T:Manor G n ι (Audited Q) I}{p:BudgetPoint}(R:ι→Support n)(Z:Set ι)
variable (V:Rep G n)
variable {d:ℕ}{F:Labels.Frame G d}{C:SectionData F}{M N: Source.Coefficient F n}{x Y D :ℝ}
local notation "W"=> Ethereal.stem

def plus (M N : Source.Coefficient F n) : Coefficient F n:= ⟨M.x+N.x, Sum.elim M.support N.support ∘ Ethereal.stem, Sum.elim M.regular N.regular ∘ Ethereal.stem,M.forced+N.forced⟩
local notation "M'"=> plus M N
variable {u:Site n}{A:Hol G}
lemma tied (hp:M.Format u A V)(hn:N.Format u A V) : (M').Format u A V:=by
   have hv k : V.p.Regular ( (M').support k) ((M').regular k) ∧ u ∈(M').support k ∧ Reads A u ((M').support k) (0: Label G d) ((M').regular k):=by
       unfold Fallow.plus; dsimp only [Function.comp_apply]; cases W k with
        | inl i=> exact ⟨hp.smooth _,hp.origin _,(reads_null_iff ..).mpr ⟨hp.identity_null _,hp.projects _⟩⟩
        | inr i=> exact ⟨hn.smooth _,hn.origin _,(reads_null_iff ..).mpr ⟨hn.identity_null _,hn.projects _⟩⟩
   have hR:ForceFormat V.p V.activities u (M.forced+N.forced) := ForceFormat.add ⟨hp.forcing,hp.carried,hp.invariant,hp.supported,hp.borel⟩ ⟨hn.forcing,hn.carried,hn.invariant,hn.supported,hn.borel⟩
   exact ⟨fun i=> (hv i).1,fun i=>(hv i).2.1,fun i=> ((reads_null_iff ..).mp (hv i).2.2).1, fun i=> ((reads_null_iff ..).mp (hv i).2.2).2,hR.forcing,hR.carried,hR.invariant,hR.supported,hR.borel⟩
lemma added (hM:M.remBound u V D x)(hN:N.remBound u V D Y): (M').remBound u V D (x+Y):=by
   obtain ⟨a,b,ha,hb,hB,hD,⟨f,hF,hV⟩,hA⟩:=hM
   obtain ⟨t,d',ht,hc,hp,hW,⟨r,hT,h⟩,hΩ⟩:=hN
   have hG:= ForceCost.add (show ForceCost V.p V.activities M.forced _ from hA) (show ForceCost V.p V.activities N.forced _ from hΩ)
   rw [←mul_add] at hG
   let F:=Sum.elim f r
   refine ⟨a+t,b+d',add_nonneg ha ht,add_nonneg hb hc,by linarith,hD,⟨F∘ Ethereal.stem, ?_,?_⟩,hG⟩
   · let g i:= V.p.mass (Sum.elim M.support N.support i) (F i); exact Extra.Iteration.Cost.equiv Ethereal.stem (show SumBudget g _ from Extra.Iteration.Cost.sum hF hT)
   intro i; unfold plus; dsimp only [Function.comp_apply]; cases W i with
                                                       | inl i=> exact hV _
                                                       | inr i=> exact h _
lemma jointly (V':Config G n) (hM:M.remBound u V D x)(hN:N.remBound u V D Y): (M').exponentialEntry u C V V'= M.exponentialEntry u C V V'+N.exponentialEntry u C V V' :=by
   have hm:= Coefficient.regular_series hM|>.summable V'; have hn:=Coefficient.regular_series hN|>.summable V'
   let A:= Sum.elim (fun i=>M.maskedTerm V i V') (fun i=> N.maskedTerm V i V'); have he (i:ℕ): (M').maskedTerm V i V'=A (Ethereal.stem i):= by unfold Coefficient.maskedTerm plus; dsimp only [Function.comp_apply]; cases Ethereal.stem i <;> rfl
   let Hw v:= Local.primary C u V.p.threshold v V'; have hp : ∀ v w, Hw (v+w)=Hw v+Hw w:= by intro v w; unfold Hw; simp
   unfold Coefficient.exponentialEntry; simp_rw [he]; rw [Ethereal.stem.tsum_eq A]; change Hw (M.x+N.x)+(∑' i, A i)= (Hw M.x+_)+(Hw N.x+_); rw [hp, Summable.tsum_sum (f:=A) hm hn]; abel_nf; rfl
lemma emptyF (V:Activities G n)(u:Site n)(p:BudgetPoint): Local.ForceFormat p V u 0∧ Local.ForceCost p V (0:ℕ→ Config G n→ℂ) 0 :=
   ⟨⟨fun _ _ h=>(h rfl).elim,fun _ h=>(h rfl).elim,fun i s x=>rfl,fun _ _ _ _ _=>rfl,fun _=> measurable_const⟩,⟨0,(by unfold BudgetPoint.mass; simp only [Pi.zero_apply,mul_zero]; exact sumBudget_zero (le_refl _)), fun _=>by simp⟩⟩
end YM.RemainderComparison.Fallow
