import YM.MSbar.Alto.Gainer
import YM.Extra.ITERATION_NO_LOSS.Gates
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
open Supply Input Push.PriceCompiler
variable (h:G.Simple) {B:Sheet G}{L:Rolls B}(P:Protection L) (K:MapPrices)(O:ChartRatio G)
variable (hh:∀ j:ℕ, BeforeL j (L.L j) K G) (j:ℕ)
include h hh
lemma tender : ∀ᶠ x:ℝ in atTop,∀ s≤j,∀ p≤j,∀ i≤j,∀ A:Patch,A.J=j→A.L=L.L j→6≤ s→Request K O (B.profile j) j i B.kernel A s p x :=by
    by_cases hj:4≤j
    · let X:Finset ℕ:= Finset.range (j+1)
      let g:= L.L j; let A:Patch:=⟨g,j,hj,(L.large j).size,(L.large j).odd⟩
      suffices he: ∀ᶠ x:ℝ in atTop,∀ s∈ X,∀ p∈X,∀ i∈X,6 ≤ s → Request K O (B.profile j) j i B.kernel A s p x by
        filter_upwards [he] with t ht s hs p hp i hi A' hA hh hz; have hv:A'= A:=by cases A'; unfold A g; congr
        rw [hv]; exact ht _ (mem_range.mpr (by omega)) _ (mem_range.mpr (by omega)) _ (mem_range.mpr (by omega)) hz
      refine X.eventually_all.mpr fun s hs=> X.eventually_all.mpr fun p hp=> X.eventually_all.mpr fun i hi=> ?_; by_cases hS:6 ≤ s
      · have ht : Host G (seats K j i s) g p s (ceilα K j i):= hh j|>.1 p s hS (Nat.lt_succ_iff.mp (mem_range.mp hs)) (Nat.lt_succ_iff.mp (mem_range.mp hp)) i (Nat.lt_succ_iff.mp (mem_range.mp hi))
        exact (need s p h K j i O (B.profile j) A ht rfl B.kernel).mono fun x hx _ =>hx
      exact Eventually.of_forall fun x hx=> (hS hx).elim
    exact Eventually.of_forall fun x _ _ _ _ _ _ A he _ _=> (hj (le_trans A.order_cut he.le)).elim
variable {T:Delays P}
lemma beta_link {W:Bar T}(w:Wait W)(A:Levels G)(hz:Paid w A)(m p:ℕ): A.clock.hatBeta (m+1)= countV G ((A.clock.op m p).patch.L) (A.clock.hatBeta m):=by
    unfold Calendar.hatBeta countV; rw [Schedule.scale_succ]; change _=_+_ * Real.log (A.clock.schedule.block m).val; ring
omit h hh in
lemma ships (j:ℕ): ∀ᶠ n:ℕ in atTop,∀ x∈Finset.range (j+1),∀ g:Side,n=g.val→ Sampled g (B.profile x) := (Finset.range _).eventually_all.mpr fun x _=> retreat (B.profile x)
-- Purchase shell and delay together; no Wait needed

structure Reports (K:MapPrices)(B:Sheet G)(O:ChartRatio G)(A:Levels G) : Prop where
    pulse m p : Sampled (A.S.side m p) (A.params m)
    stage m p s r: s ≤ A.clock.J (m+1) → r ≤ A.clock.J (m+1) → 6 ≤ s → Request K O (A.params (m+1)) (A.clock.J (m+1)) (A.clock.J m) B.kernel (A.clock.op m p).patch s r (A.clock.hatBeta m)
lemma album (p:Delays P):∃ Q:Delays P,DelayLe p Q∧∀ V:Delays P,DelayLe Q V→∀ (W:Bar V)(w:Wait W)(A:Levels G),Paid w A→ Reports K B O A:=by
    choose f hf using fun j=> eventually_atTop.mp (tender h _ O hh j)
    choose g hg using fun j=> eventually_atTop.mp (ships (B:=B) j)
    let Q:Delays P:={p with shells:=fun i=>max (p.shells i) (g i),
                                        betaEntry:=fun i=>max (p.betaEntry i) (f i)}
    refine ⟨Q,⟨fun i=>le_max_left ..,le_rfl,fun i=>le_max_left .., le_rfl⟩,fun V he W w A hv=>?_⟩
    have hh(i):A.params i = B.profile (A.clock.J i):=by unfold Levels.params Calendar.params; rw [hv.stage]
    have hT(m p:ℕ) : (A.clock.op m p).patch.L=L.L (A.clock.J (m+1)):=by change A.S.block m= _; rw [←A.fits.sameFactor, hv.lengths]
    constructor
    · intro m p; rw [hh]; apply hg (A.clock.J (m+1)) (A.S.side m p).val _ _ _ _ rfl
      · let j:= A.clock.J (m+1); apply le_trans (b:=Q.shells j) (le_max_right ..); apply (he.shells j).trans (le_trans _ (hv.volume m p)); apply Nat.le_mul_of_pos_right; positivity
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (A.fits.mono (Nat.le_succ m)))
    intro m p s r hs hr h; rw [hh]; let j:= A.clock.J (m+1); exact hf j (A.clock.hatBeta m) (le_trans (b:=Q.betaEntry j) (le_max_right ..) ((he.beta j).trans (hv.pays m))) s hs r hr _ (A.fits.mono (Nat.le_succ _)) _ rfl (hT ..) h
end YM.MSbar.Alto
