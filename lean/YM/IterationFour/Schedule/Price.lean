import YM.IterationFour.Schedule.Provider
import YM.IterationFour.Vacuum.License

/-!
# Ask affordances before/after L on the same witness

Arbitrary pre-L stage asks (coarse and fine) on the block lengths, then
post-L asks on the common delays. In using with e.g. WilsonX, choose the
packet-width/strip, initial kernel etc demands on the PRE port, not after.
The marker and vacuum comparisons can use `post` e.g. to pay finite lists of
derivative costs. Not supplying qcert's stronger scheduling demands (e.g.
analysis windows at more than one stage).
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Clock
open Lattice Wilson RG RG.Supply Function Filter Currency Spending
open AnalyticBridge VerifiedReset
open scoped Topology BigOperators ContDiff
variable {G : Gauge}

/-- z convention of qcomp. -/
def doubleLog (a : Levels G) (m : ℕ) := 1+Real.log (Real.log (a.clock.hatBeta m))
lemma doubleLog_late (a : Levels G) (hg : G.Simple) : Tendsto (doubleLog a) atTop atTop := by
  exact tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate a hg)))
lemma smallDouble (a : Levels G) (hg : G.Simple) : Spending.Slip a (doubleLog a) := by
  refine (monitor_cost a hg).relax ?_
  filter_upwards [(doubleLog_late a hg).eventually_ge_atTop 2] with i hi
  have ht:= Real.add_one_le_exp ((doubleLog a i-1)^2)
  rw [show doubleLog a i - 1 = Real.log (Real.log (a.clock.hatBeta i)) from (by unfold doubleLog; ring)] at ht
  apply le_trans ?_ (le_abs_self _); change |doubleLog a i| ≤ Real.exp _
  rw [abs_of_pos (show 0<doubleLog _ _ by linarith)]; unfold doubleLog at *; nlinarith

/-- Buy pre/delay amounts without rechoosing, require at **every** stage. -/
abbrev PriorNeed := ℕ→ Stage → ℕ → Stage → ℕ
abbrev DelayNeed := ℕ→ Stage → ℕ → Stage → Side →ℝ
structure Register (a : Levels G) (f : PriorNeed) (g : DelayNeed) : Prop where
    palace i : let J:=a.clock.J; let p:=a.params
               f (J (i+1)) (p (i+1)) (J i) (p i) ≤ (a.S.block i).val
    powers i : ∃ k : ℕ, (a.S.block i).val = 3^k
    complete i : let J:=a.clock.J; let p:=a.params
                 |g (J (i+1)) (p (i+1)) (J i) (p i) (a.S.block i)| ≤ doubleLog a i ∧
                 ((a.S.block i).val : ℝ) ≤ doubleLog a i

variable (f : PriorNeed) (g : DelayNeed)
def FitsPrior {P : Sheet G} (D : Rolls P) : Prop := ∀ i j, i≤j → j ≤ i+1 →
    f j (P.profile j) i (P.profile i) ≤ (D.L j).val

lemma prior (hg : G.Simple) (P : Sheet G) : ∃ D : Rolls P,FitsPrior f D ∧ ∀ i,∃ k : ℕ,(D.L i).val=3^k := by
  -- arbitrary growth through the options j and j-1
  choose M hM using fun i=> Rolls.eventually_large P hg i
  let u i:= max (M i) (max (f i (P.profile i) i (P.profile i)) (f i (P.profile i) (i-1) (P.profile (i-1))))
  let U i:= (Finset.range (i+1)).sup u
  have hU (i): u i≤U i:= Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _))
  have hm:Monotone U:=fun _ _ he=> Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right he _))
  let L (j : ℕ): Side := ⟨3 ^ U j,pow_pos (by decide) _⟩
  have he j: u j ≤ (L j).val :=by
     refine (hU j).trans ?_
     exact (Nat.lt_two_pow_self.le).trans (pow_le_pow_left' (by norm_num) (U j))
  let D : Rolls P:=⟨L,fun j=> hM _ _ ((le_max_left ..).trans (he j)) (((show Odd (3:ℕ) from ⟨1,rfl⟩).pow)),fun i j h => pow_le_pow_right' (show 1 ≤ (3:ℕ) by decide) (hm h)⟩
  refine ⟨D,fun i j hx hy=>?_,fun i=> ⟨U i,rfl⟩⟩
  rcases Nat.eq_or_lt_of_le hx with h|h
  · subst j; exact ((le_max_left ..).trans (le_max_right ..)).trans (he i)
  rw [show i=j-1 by omega]; exact ((le_max_right ..).trans (le_max_right ..)).trans (he j)

lemma delayed {P : Sheet G} {D : Rolls P} (θ : Protection D) (hf : FitsPrior f D)
    (hh : ∀ i, ∃ k : ℕ,(D.L i).val=3^k) : ∃ T : Delays θ, ∀ {W : Delays θ}, Push.PriceCompiler.DelayLe T W →
      ∀ (b : Bar W) (J : Wait b) (a : Levels G), Paid J a → Register a f g := by
  let Y j i:= g j (P.profile j) i (P.profile i) (D.L j)
  let S j:= max ((D.L j).val:ℝ) (max (|Y j j|) (|Y j (j-1)|))
  let z x:= 1+ Real.log (Real.log x)
  have he : Tendsto z atTop atTop:=tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  choose u hu using fun i=> eventually_atTop.mp (he.eventually_ge_atTop (S i))
  refine ⟨⟨u,fun _ _=>0,fun _=>1,fun _=>1⟩,fun hX b J a h=>?_⟩
  have ht i : (D.L (a.clock.J (i+1)))=a.S.block i:= by rw [← h.lengths]; exact a.fits.sameFactor ..
  have hV i : a.params i=P.profile (a.clock.J i):= congr_fun h.stage _
  have hp i:= a.fits.mono (Nat.le_succ i)
  have hv i:=a.fits.stepSlow i
  refine ⟨fun i=>?_,fun i=> ht i ▸ hh _,fun i=>?_⟩
  · dsimp only; rw [hV (i+1),hV i,← ht i]; exact hf _ _ (hp i) (hv i)
  dsimp only; rw [hV (i+1),hV i, ← ht i]
  let j:=a.clock.J (i+1); let p0:=a.clock.J i
  have hΩ : S j ≤ doubleLog a i:=hu j _ ((hX.beta j).trans (h.pays i))
  change |Y j p0| ≤ doubleLog a i ∧ _
  have h₀: p0 ≤ j:=hp i; have h₁:j≤p0+1:=hv i
  refine ⟨(le_trans ?_ (show max (|Y j j|) (|Y j (j-1)|) ≤ doubleLog a i from (le_max_right ..).trans hΩ)), (le_max_left ..).trans hΩ⟩
  rcases (show p0=j ∨ p0=j-1 by omega) with h|h
  · rw [show Y j p0=Y j j from h ▸ rfl]; exact le_max_left ..
  rw [show Y j p0=Y j (j-1) from h ▸ rfl]; exact le_max_right ..

-- arbitrary books at different ξ are not compatible. choose the prebook with all such ξ *before*.
lemma rider (hg : G.Simple) : PhysicalNext.Repeat.Legato.IterationFour.Rider (G:=G) (fun a=> Register a f g) := by
  intro s
  obtain ⟨D,hD,H⟩:= prior f hg s
  refine ⟨D,fun θ=>?_⟩
  obtain ⟨T,hT⟩:= delayed f g θ hD H
  refine ⟨T,fun V hV b W=>?_⟩
  obtain ⟨a,ha,hX⟩:= Wait.engine W hg
  exact ⟨W,⟨le_rfl,le_rfl,le_rfl⟩,a,ha,hX,hT hV b W a ha⟩

-- Mint.Slow actually available jointly with honors for every other f,g.
include f g
lemma riderSlow (hg : G.Simple) : PhysicalNext.Repeat.Legato.IterationFour.Rider (G:=G)
      (fun a=> Register a f g ∧ Vacuum.Mint.Slow a) := by
  let y : DelayNeed := fun j p i q s=> |g j p i q s| + |Time.base G q| + |Time.softCeiling G q 1|
  intro s
  obtain ⟨D,hD,H⟩ := prior f hg s
  refine ⟨D,fun θ=>?_⟩
  obtain ⟨T,hT⟩ := delayed f y θ hD H
  refine ⟨T,fun V hV b W=>?_⟩
  obtain ⟨a,ha,hX⟩:= Wait.engine W hg
  have hf:= hT hV b W a ha
  have hh i:= hf.complete i
  have hz (i : ℕ) : |g (a.clock.J (i+1)) (a.params (i+1)) (a.clock.J i) (a.params i) (a.S.block i)| + |Vacuum.adjusting a i|+|Time.softCeiling G (a.params i) 1| ≤ doubleLog a i:= (le_abs_self _).trans (hh i).1
  have hx : ∀ i, ∃ Q:ℝ, |Vacuum.adjusting a i|+|Time.softCeiling G (a.params i) 1| ≤ Q ∧ Q ≤ |doubleLog a i| := by
    intro i; have he:= hz i
    exact ⟨doubleLog a i,(by linarith [abs_nonneg (g (a.clock.J (i+1)) (a.params (i+1)) (a.clock.J i) (a.params i) (a.S.block i))]),le_abs_self _⟩
  have he := smallDouble a hg
  refine ⟨W,⟨le_rfl,le_rfl,le_rfl⟩,a,ha,hX,⟨hf.palace,hf.powers,fun i=>?_⟩,
    he.relax (Eventually.of_forall (fun i=>?_)),he.relax (Eventually.of_forall (fun i=>?_))⟩
  · refine ⟨?_,(hh i).2⟩
    linarith only [hz i, abs_nonneg (Time.softCeiling G (a.params i) 1),abs_nonneg (Vacuum.adjusting a i)]
  · obtain ⟨Q,hq,hb⟩:=hx i; exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hq.trans hb)
  obtain ⟨Q,hq,hb⟩:= hx i; exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hq.trans hb)

open UVExtension
/-- Direct financial instance supplier. -/
theorem beginning (hG : G.Simple) {x : ℝ} (hx : 0 < x) :
    ∃ (C : Family G) (J : Extraction.Order) (T : Table C.book)
        (F : Spec.Final C J T) (L : EveryPhase.Almanac F),
      C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=x ∧
      Oasis.Floral (hG:=hG) C ∧
      (Register C.path.levels f g ∧ IterationFour.Vacuum.Mint.Slow C.path.levels) ∧
      (Extraction.Order.mk Extraction.Sequence.full J.per).Ordered C T ∧
      (∀ d k:ℕ,∀ᶠ n in atTop,
          ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i,(v i).1≤d) →
            ∃ g,Poppy.Margins C r n k v g) ∧ EveryPhase.Completed F L:=
  PhysicalNext.Repeat.Legato.IterationFour.acceptedWith hG hx (riderSlow f g hG)
end YM.IterationFour.Clock
