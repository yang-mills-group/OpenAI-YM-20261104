import YM.Integration.WilsonThermometerOffsetGraph

/-! Follow the actual residue of one selected microscopic point through every
block. The signed graph starts with the original bare field and measures the
transfer in the inverse-normalized reporting coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetTrajectory
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Trace.Physical OPE MergeProof Push Local
open PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {d N p base : ℕ} {D : Rail C}
    {B : ℕ → ℕ → ℝ}
structure Enrolled (h : C.Makes) (D : Rail C) (B : ℕ → ℕ → ℝ)
    (base N p d : ℕ) (sites : ∀ i, Bud C p i)
    (V : Sight C d p) (r : Emblems C d) : Prop where
  starts : V N = basisTop C d N p
  legal (m : ℕ) : base ≤ m → m ≤ N → Group C N m p d (V m) (B d m)
  follows (m : ℕ) : base ≤ m → ∀ live : m<N,
    WilsonThermometerOffsetGraph.Transfer (D:=D N p m live) h live (sites m) (V (m+1)) (V m) (r m)

theorem enroll (h : C.Makes) (awake : Awake D B base d) (live : base≤N)
    (sites : ∀ i, Bud C p i) :
    ∃ V r, Enrolled h D B base N p d sites V r := by
  induction live using Nat.decreasingInduction with
  | self =>
    let V : Sight C d p := update (fun _ => 0) N (basisTop C d N p)
    refine ⟨V,(fun _ => LinearEquiv.refl _ _), update_self ..,?_,fun i hi low => by omega⟩
    intro i hi reached
    obtain rfl : i=N := le_antisymm reached hi
    unfold V; rw [update_self]
    have top := basis_paid (d:=d) (p:=p) h awake.post
    exact ⟨fun x => let ⟨v,hv⟩ := top.capacity0 x; ⟨v,hv.grow
      (mul_le_mul_of_nonneg_right (awake.cash _ le_rfl) (size_ge _))⟩,
      top.pos.trans (awake.cash _ le_rfl)⟩
  | of_succ k hk ih =>
    obtain ⟨V,r,track⟩ := ih (show Awake D B (k+1) d from
      ⟨fun i hi => (awake.post i hi).trans k.le_succ,
       fun i hi => awake.cash i (k.le_succ.trans hi),
       fun p i N hi => awake.toll p i N (k.le_succ.trans hi)⟩)
    obtain ⟨W,q,payment,ride⟩ := WilsonThermometerOffsetGraph.step h hk
      (awake.toll p k N le_rfl hk) (track.legal (k+1) le_rfl hk) (sites k)
    refine ⟨update V k W,update r k q,?_,?_,?_⟩
    · rw [update_of_ne hk.ne']; exact track.starts
    · intro i hi hj
      by_cases he : i=k
      · subst i; rw [update_self]; exact payment
      rw [update_of_ne he]; exact track.legal i (by omega) hj
    intro i hi low; rw [update_of_ne (show i+1≠k by omega)]
    by_cases he : i=k
    · subst i; rw [update_self,update_self]; exact ride
    rw [update_of_ne he,update_of_ne he]; exact track.follows i (by omega) low

theorem Enrolled.inverse {h : C.Makes} {sites : ∀ i, Bud C p i}
    {V : Sight C d p} {r : Emblems C d} (H : Enrolled h D B base N p d sites V r)
    {m j : ℕ} (begun : base ≤ m) (away : m ≤ j) (reached : j ≤ N) (x : Palette C d) :
    size (finer r away x) ≤ stringCost C away * size x := by
  induction j,away using Nat.le_induction with
  | base => simp only [base_value,string_base,LinearEquiv.refl_apply,one_mul,le_rfl]
  | succ j away ih =>
    let x' := finer r away x
    have inv := (H.follows j (begun.trans away) reached).payment ((r j).symm x')
    rw [(r j).apply_symm_apply] at inv
    rw [finer_next away,string_next away,mul_assoc]
    exact (le_trans (size_refund ..) inv.1).trans
      (mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le reached)) (zero_le_one.trans (lamp_nn _)))

theorem original (R : Run G) (simple : G.Simple) (paid : RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ B : ℕ → ℕ → ℝ, ∀ d (ε : ℝ), 0<ε → ∀ᶠ m : ℕ in atTop,
      ∀ p N, m≤N → ∀ sites : ∀ i, Bud R.family p i,
        ∃ V r, Enrolled R.makes R.doors B m N p d sites V r ∧
          ∀ j (away : m≤j), j≤N → ∀ x : Palette R.family d,
            size (finer r away x) ≤ Real.exp (ε*(R.family.S.scale j-R.family.S.scale m))*size x := by
  obtain ⟨B,buys⟩ := held (WilsonCloseCaptureSignedPrice.purchased R simple paid)
  refine ⟨B,fun d ε gain => ?_⟩
  filter_upwards [buys d, string_paid (C:=R.family) gain] with m awake cost p N live sites
  obtain ⟨V,r,track⟩ := enroll R.makes awake live sites
  exact ⟨V,r,track,fun j away reached x => (track.inverse le_rfl away reached x).trans
    (mul_le_mul_of_nonneg_right (cost j away) (size_ge _))⟩

end YM.Integration.WilsonThermometerOffsetTrajectory
end
