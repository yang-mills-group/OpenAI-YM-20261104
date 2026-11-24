import YM.IterationFour.Vacuum.Price

/-!
# Pinned unmarked induction on actual density histories

Conditional on common LOCAL comparison incl startup, concrete coefficients,
prices. Choose ONE output at every level with identity on entire `eval`, not
just interior. Keep the certificates of how it was assembled (e.g. so joint
mark budgets can consume `Deposited` on this output). Whenever comparing
multiple cutoffs these estimates are cutoff uniform, not a near-cutoff local
step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum
open Lattice Wilson RG Function MeasureTheory Filter Currency Render
open AnalyticBridge VerifiedReset Collection
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {N q r : ℕ}

/-- The operation at fixed cutoff. -/
def advance (C : Family G) (N q i : ℕ) (S : List (Piece G (C.side (i+1) q)))
    (U : RG.Rep G (C.side (i+1) q)) : Config G (C.side i q) → ℝ :=
  (C.path.levels.clock.op i q).push (C.path.β N q (i+1)) (loaded C N q (i+1) S U).eval

variable (P : Plan C N q r) (Y : Purse)
/-- The unmarked analytic hypotheses supplied locally, *NOT* using any finer
    convergence premise. -/
structure Counter (t : ℕ→Pocket) (m : ℕ) : Prop where
    starts : ∃ X v τ, Early C N q N (P.layers N) X v τ (P.predict N) (P.alpha N)
      ((t N).due 0 (Y.guardBill C.path.levels (N+1))) (t N).forceEarly (Wilson.bare (C.beta N q))
    recursive (i : ℕ) (hi : i<N) (hp : m ≤ i) (U : RG.Rep G (C.side (i+1) q)) (x : ℝ)
      (hy : Coin C N q (i+1) (P.layers (i+1)) U x (t (i+1)).forceGoal (Y.guardBill C.path.levels (i+1)))
      (h : 0 ≤ x) (hx : x≤Y.limit C.path.levels (i+1)) :
      ∃ X v τ, Early C N q i (P.layers i) X v τ (P.predict i) (P.alpha i)
        ((t i).due x (Y.guardBill C.path.levels (i+1))) (t i).forceEarly (advance C N q i (P.layers (i+1)) U)

variable (t : ℕ→Pocket)
structure Trail where
    loss : ℕ→ ℝ
    atLevel i : RG.Rep G (C.side i q)
-- Trail needs indices explictly? structure parameters omitted if unused

/-- Deposit includes full provenance retained, not just evaluation estimates. -/
def Deposited (i : ℕ) (F : Config G (C.side i q) → ℝ) (x : ℝ) (z : ℝ) (W : RG.Rep G (C.side i q)) :=
    let H:=(t i).due x (Y.guardBill C.path.levels (i+1))
    ∃ X v τ, Early C N q i (P.layers i) X v τ (P.predict i) (P.alpha i) H (t i).forceEarly F ∧
      W = reclosed C N q i (P.layers i) X v τ (P.predict i) (P.alpha i) ∧
        z=owed C.path.levels i (P.layers i) (Y.guardBill C.path.levels i) H
structure Issued (i : ℕ) (z : ℝ) (W : RG.Rep G (C.side i q)) : Prop where
    nonneg : 0 ≤ z
    cap : z ≤ Y.limit C.path.levels i
    coupon : Coin C N q i (P.layers i) W z (t i).forceGoal (Y.guardBill C.path.levels i)
    kinetic : |P.predict i-C.path.β N q i| ≤ (Y.fare+1)*weight C.path.levels (Y.sigma-2) i
structure Aligned (m : ℕ) (L : Trail (C:=C) (q:=q)) : Prop where
    top : Deposited P Y t N (Wilson.bare (C.beta N q)) 0 (L.loss N) (L.atLevel N)
    transmits (i : ℕ) (hi : i < N) (hv : m ≤ i) : Deposited P Y t i
      (advance C N q i (P.layers (i+1)) (L.atLevel (i+1))) (L.loss (i+1)) (L.loss i) (L.atLevel i)
    costs i (hi : i ≤ N) (hv : m ≤ i) : Issued P Y t i (L.loss i) (L.atLevel i)

variable {t} {m : ℕ}
lemma single_step (hg : G.Simple) (ht : C.Makes) {i x} (hv : 0≤x) (hi : i≤N) (hx : x≤Y.limit C.path.levels (i+1))
    {F : Config G (C.side i q) → ℝ}
    (hf : ∃ X v τ, Early C N q i (P.layers i) X v τ (P.predict i) (P.alpha i)
      ((t i).due x (Y.guardBill C.path.levels (i+1))) (t i).forceEarly F)
    (he : F=(C.path.rep N q i).eval) (hr : Room C Y P i (t i))
    (hw : FixedWave C i (Y.guardBill C.path.levels i)) : ∃ U z,
      Deposited P Y t i F x z U ∧ Issued P Y t i z U := by
  obtain ⟨H,hD,hP,hN,hQ⟩:= limits P Y hg hr x hv hx
  obtain ⟨X,v,τ,hF⟩:= hf
  have hL := mul_le_mul_of_nonneg_left hx (t i|>.prices_pos.1)
  let y := (t i).due x (Y.guardBill C.path.levels (i+1)); let Q:= reclosed C N q i (P.layers i) X v τ (P.predict i) (P.alpha i)
  have hK : Duty C.path.levels i (P.alpha i) y (t i).forceEarly (t i).forceGoal :=
    Reset.cheaper C.path.levels i (add_le_add_left (add_le_add_left hL _) _) hr.hard
  obtain ⟨hu,hW,hU⟩:= resume hg C ht hi hF he hr.format hr.predicted hK hr.hard_paid
    ((Y.guard_pos C.path.levels i).le) hw ((add_le_add_left hP _).trans hr.supplies) hr.decent hr.width
  exact ⟨Q,_,⟨X,v,τ,hF,rfl,rfl⟩,⟨hN,hP,hu,hW.trans hQ⟩⟩

lemma traced (hg : G.Simple) (h : C.Makes) (H : Counter P Y t m) (hx : m ≤ N)
    (he : ∀ i, m ≤ i → i≤N → Room C Y P i (t i))
    (hw : ∀ i, m ≤ i → i≤N → FixedWave C i (Y.guardBill C.path.levels i)) :
    ∃ L, Aligned P Y t m L := by
  suffices ∀ j, (j≤N) → (m≤j) → ∃ L, Aligned P Y t j L from this m hx le_rfl
  intro j hj
  induction hj using Nat.decreasingInduction with
  | self =>
    intro hj
    obtain ⟨U,z,hD,hU⟩ := single_step P Y hg h le_rfl le_rfl (Y.limit_pos _ (N+1)|>.le)
      H.starts (h.wilson.starts N q).2.symm (he N hx le_rfl) (hw N hx le_rfl)
    let L : Trail (C:=C) (q:=q) := ⟨fun _=>z, Function.update (C.path.rep N q) N U⟩
    have hp : L.atLevel N=U := Function.update_self ..
    exact ⟨L,⟨by rw [hp]; exact hD, fun _ hi hh=> False.elim (hi.not_ge hh),
      fun i hi hh=> by
        rw [show i=N from le_antisymm hi hh]
        rw [hp]; exact hU⟩⟩
  | of_succ i hi ih =>
    intro hk
    obtain ⟨L,hL⟩ := ih (hk.trans i.le_succ)
    have hI:= hL.costs _ hi le_rfl
    have hg' := H.recursive i hi hk _ _ hI.coupon hI.nonneg hI.cap
    have hV : advance C N q i (P.layers (i+1)) (L.atLevel (i+1))=(C.path.rep N q i).eval:= by
      rw [advance,hI.coupon.value]; exact (h.wilson.steps _ _ _ hi).1.symm
    obtain ⟨U,z,hD,hx⟩ := single_step P Y hg h hI.nonneg hi.le hI.cap hg' hV (he i hk hi.le) (hw i hk hi.le)
    let L' : Trail (C:=C) (q:=q) := ⟨update L.loss i z, update L.atLevel i U⟩
    have hz : L'.atLevel i=U := update_self ..
    have hy : L'.loss i=z:= update_self ..
    have hx' (k:ℕ)(h:i<k): L'.atLevel k=L.atLevel k := update_of_ne h.ne' ..
    have hp (k:ℕ)(h:i<k): L'.loss k=L.loss k := update_of_ne h.ne' ..
    refine ⟨L',⟨?_,?_,?_⟩⟩
    · rw [hx' N hi,hp N hi]; exact hL.top
    · intro k hk he; rcases eq_or_lt_of_le he with hK|ht
      · subst k; rw [hx' _ (Nat.lt_succ_self _),hp _ (Nat.lt_succ_self _),hz,hy]; exact hD
      rw [hx' k ht, hx' _ (ht.trans k.lt_succ_self), hp k ht,hp _ (ht.trans k.lt_succ_self)]; exact hL.transmits k hk ht
    intro k hK hk
    rcases eq_or_lt_of_le hk with hK'|hq
    · subst k; rw [hz,hy]; exact hx
    rw [hp k hq,hx' k hq]; exact hL.costs k hK hq
end YM.IterationFour.Vacuum
