import YM.RGComparison01.High
import YM.UVExtension.Oasis.Flora
import YM.Pert.Asymptotics.RawAxis

/-! # High tails at the actual step, on *each* chosen physical common witness.
Shares all scales, layout, supports, and unmarked vacuum data; no new `Final`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Tree Wilson Finset
open ConnectedActivityE6 Shoot Precision
open PhysicalNext PhysicalNext.Repeat Song
open AnalyticBridge VerifiedReset Collection
open UVExtension Legato Input Org Supply Push.PriceCompiler Opera
open scoped Topology BigOperators Classical

section high
variable {G : Gauge} {hG : G.Simple} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {F : Roost.Factor A}
    {J : Spire.Uses F hG} {t : ℕ→ℕ} {W : Bid.Worth} {B : ℕ→ℝ} {U : Bandage F B W} (L : Mast.Cellar J t U)

/-- This body explicitly identifies `PreReset` and its expansion base to the
same Family cutoff step. Use at every call on the supplied witness
(regardless of later phase/extraction). `H` is the chart used to express
analytic component terms. To get the formula for pushing/evaluating and
price, unfold `PreReset`; it is not a norm measured in arbitrary coordinates.
-/
def CommonHigh (m N n k : ℕ) : Prop :=
  let C := Mast.Cellar.yard (Mast.roseA J) L
  let R := C.path.rep N n (m+1)
  let sizes := (C.S.oneStep m n).exact_size
  C.path.β N n (m+1) ∈ Shoot.band A.B.a (m+1) ∧
  0 < R.beta ∧
  0 < Pert.Asymptotics.regulatorRun C N n (m+1) ∧
  Pert.Asymptotics.regulatorRun C N n (m+1) = Coin.coupling R.beta ∧
  C.path.levels.clock.op m n = Pane.panel A m sizes ∧
  C.path.levels.budget m = A.B.a.budget m ∧
  (C.path.rep N n m).eval = (Pane.panel A m sizes).push R.beta R.eval ∧
  R.p = A.B.a.budget (m+1) ∧ (C.path.rep N n m).p = A.B.a.budget m ∧
  R.path = A.B.kin.path N (m+1) ∧ R.clip = (A.B.a.params (m+1)).clip ∧
  (C.path.rep N n m).path = A.B.kin.path N m ∧
  ∃ H : Boulevard.Chartlet F.shape A N m sizes R,
    Boulevard.SeekR F.shape A N m sizes H ∧ High.PreReset F sizes R H k

theorem physical_high (k : ℕ) (h : (Mast.Cellar.yard (Mast.roseA J) L).Makes) :
    ∀ᶠ m in atTop, ∀ (n N : ℕ), m<N → CommonHigh L m N n k := by
  filter_upwards [High.eventually_pays F hG k] with m ht n N hm
  unfold CommonHigh
  intro C R sizes
  have hl := (J.ticking N n (Spire.Uses.centerP _)).prices
  obtain ⟨hx,hB⟩:= hl (m+1) (Nat.zero_le _) hm
  obtain ⟨H,hH⟩ := Opera.feature A.B F.shape hm F.pledging.conducts.full F.pledging.conducts.income hx hB
  have hb : 0 < R.beta := (half_pos (zero_lt_one.trans (A.B.a.fits.delayed (m+1)))).trans_le hB.1
  have hp := hx.path
  have hK := (hl m (Nat.zero_le _) hm.le).1
  exact ⟨hB,hb,Coin.coupling_pos hb,rfl,rfl,rfl,(h.wilson.steps _ _ _ hm).1,hx.point,hK.point,
    (by rw [A.B.bases] at hp; exact hp),hx.clip,
    (by have hz:=hK.path; rw [A.B.bases] at hz; exact hz),H,hH,ht N hm _ _ sizes R hB H hH⟩
end high

/-- A completely supplied analytic subestimate (not the whole analytic clause).
`k` arbitrarily high, all allowed periods and cutoffs. -/
theorem physical_tail {G : Gauge} (hG : G.Simple) {C : Family G} {f : Extraction.Order}
    {Y : Table C.book} (F : Spec.Final C f Y) (h : Oasis.Floral (hG:=hG) C) :
    ∃ (M : Metals G) (P : Rolls M.p) (A : Alloy M P)
      (B : Roost.Factor A) (J : Spire.Uses B hG) (t : ℕ → ℕ) (K : ℕ → ℝ) (w : Bid.Worth)
      (Q : Bandage B K w) (L : Mast.Cellar J t Q),
      C = Mast.Cellar.yard (Mast.roseA J) L ∧
      ∀ k, ∀ᶠ m in atTop, ∀ (n N : ℕ), m<N → CommonHigh L m N n k := by
  obtain ⟨M,P,A,B,J,Y0,t,K,w,Q,L,_,hC,_⟩:=h
  exact ⟨M,P,A,B,J,t,K,w,Q,L,hC,fun k => physical_high L k (hC ▸ F.room.cutoff)⟩
end YM.RGComparison01
