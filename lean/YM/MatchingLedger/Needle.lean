import YM.RG12.Joint.MeasureLimit
import YM.Work.E01
import YM.Work.E09

/-!
# Post-L expenses for the matching-problem solution attempt

Uses the actual f756 Couture option, *any* prescribed companion Decal.
Do not specialize this to constructions without the appropriate receipt. Keep Family, Levels,
calibration, representations and extraction. This is a commuting interface, not a claim that
all the steps can be funded at this chronology.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Pins
open Filter Function Lattice RG RG.Supply Precision Pressure
open Push.PriceCompiler PhysicalNext PhysicalNext.Repeat Daisy.Charity.RG12
open UVExtension UVExtension.Mast
open scoped Topology BigOperators Classical ContDiff

structure After (G : Gauge) where
  wants : Patch → KernelChoices → ℕ → ℝ → Prop
  sustained (n : ℕ) (P K) (_h : P.Branches K G) : ∀ᶠ β in atTop, wants P K n β

variable {G : Gauge} (X : After G)

-- can extend before consumption, same as decal.paired
def After.coin (X Y : After G) : After G where
  wants P K n b := X.wants P K n b ∧ Y.wants P K n b
  sustained n P K h:= (X.sustained n P K h).and (Y.sustained n P K h)

def Prepared (L : Levels G) : Prop := ∀ k p n : ℕ, n ≤ L.clock.J (k+1) →
  X.wants (L.clock.op k p).patch L.clock.kernel n (L.clock.hatBeta (k+1))

private def mark (Y : Teller G)(L : Side)(n : ℕ)(x : ℝ) := ∀ (P : Patch), P.J=n → P.L=L → P.Branches Y.bind G → ∀ j≤ n, X.wants P Y.bind j (betaF G x L)

private lemma patch_eq {P P' : Patch} (h:P.L=P'.L)(he:P.J=P'.J): P=P':=by cases P; cases P'; congr

/-- Order-index is the k+1 smoothing stage, x is coarse reference (NOT actual β). -/
def thread : Decal G where
  rub Y _ _ L _ _ _ _ n x:= mark X Y L n x
  good P Q E:= by
    refine ⟨0,fun L _ _ _ _ _ i _ _ _=>?_⟩
    by_cases hu:∃ Z:Patch,Z.J=i ∧ Z.L=L ∧ Z.Branches P.bind G
    · obtain ⟨V,hv,hx,h⟩:=hu
      filter_upwards [eventually_all.mpr (fun j:Fin (i+1)=> (Work.E09.betaF_growth G L).eventually (X.sustained j V P.bind h))] with b ht Z hZ hQ hB j hj
      rw [show Z=V from patch_eq (hQ.trans hx.symm) (hZ.trans hv.symm)]; exact ht ⟨_,Nat.lt_succ_of_le hj⟩
    exact Eventually.of_forall fun _ R H W h => (hu ⟨R,H,W,h⟩).elim

variable {C : Family G} {hG:G.Simple} {δ:Decal G}
variable (T:Couture C hG (δ.paired (thread X)))

lemma paired_left : Mallow.RG12.Earned δ T.factor.shape T.cost.delay:= fun a b x i h => (T.couture a b x i h).1

set_option maxHeartbeats 360000 in
include T in
lemma purchased : Prepared X C.path.levels := by
  let L:= T.cost.B.a; let Z:= T.factor
  have hE : C.path.levels = L := congr_arg (fun R:Family G => R.path.levels) T.belongs
  rw [hE]; intro i p n hp
  let x := L.clock.J (i+1); let y:= L.clock.hatBeta i
  let Q := (L.clock.op i p).patch; let d:=T.roll.L x
  have hx := (T.couture x y (T.cost.B.valid.pays i) (L.clock.J i) (step_paid L i)).2
  let K:=T.metal.p.kernel
  have ht: L.clock.kernel=K:=T.cost.B.valid.kernel
  have he: X.wants Q K n (betaF G y d):= hx Q rfl (block_eq T.cost.B.valid i) (show Q.Branches K G from ht ▸ (L.blocks i p).branches) n hp
  rw [show L.clock.hatBeta (i+1)=_ from (show _= betaF G y d from beta_eq T.cost.B.valid i),ht]
  exact he

lemma later_cost (L : Levels G) (he:Prepared X L)(n:ℕ) :
    ∀ᶠ m in atTop, ∀ i:ℕ, X.wants (L.clock.op m i).patch L.clock.kernel n (L.clock.hatBeta (m+1)):=by
  filter_upwards [L.fits.deep.eventually_ge_atTop n] with k hk i
  exact he k i n (hk.trans (L.fits.mono (Nat.le_succ _)))

end YM.MatchingLedger.Pins
