import YM.Integration.WilsonMixedTaggedMeasuredReserve
import YM.Integration.WilsonMixedTaggedUnweight

/-! The true late reporting date pays the unweighted regular and forced site
sums at every close date and on all held fields. A fixed leading constant
also covers the two-endpoint three-slot comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedMeasuredBudget
open Filter Finset Function Lattice Wilson RG Marker MergeProof Accent Push GridApprox.Nil
open PhysicalNext.Repeat.Legato RG05Readout Many
open scoped Topology BigOperators Classical
variable {G:Gauge}

/-- Every lower ward monomial uses at most the prescribed number of
physical colors, even though the collection of fine address names grows. -/
theorem cardinal {U V:Type} [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V]
    (B:Census V) (π:U → V) (s:(Lift B π).Mode) : s.val.card ≤ Fintype.card V := by
  have lit:Lit B π s.val := (Finset.mem_filter.mp s.property).2
  exact lit.keep_count ▸ Finset.card_le_univ (s.val.image π)

/-- Each actual weighted output, regular or forced, can use this same reserve.
The support type and the physical field are chosen after the date and D. -/
theorem original (R:Run G) (simple:G.Simple)
    (K d k h L p:ℕ) (hk:0 < K) {c ε:ℝ} (cp:0 < c) (ep:0 < ε)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG05Readout.Lambda R.family.path.levels j)) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), let C:=R.family
      let b:=crossLevel C.S r-1-1
      let m:=WilsonMeasuredWindow.stop C.path.levels simple K r
      let B:=(C.path.levels.budget m).B
      let β:=C.path.levels.clock.hatBeta m
      ∃ D:ℕ, D*(4*B+2)+2*B ≤ B^2 ∧ ∀ N:ℕ, m ≤ N → ∀ per:ℕ,
        let g:=(Real.sqrt (C.path.rep N per m).beta)⁻¹
        ∀ i:ℕ,b ≤ i → i ≤ m → ∀ {V I:Type} [DecidableEq V] [Fintype I] {J:Census V}
          (Q:V → ℝ),(∀v,0 < Q v) → (∀v,Q v ≤ β^h) → (∀s:J.Mode,s.val.card ≤ L) → 
          ∀ (S:I → Support (C.side i per)) (F:I → Config G (C.side i per) → Poly J) (B':ℕ)(α δ:ℝ),
            0 < δ → δ ≤ c*(β^((k+h)*L)*Real.exp (-(D:ℝ))) → 
            Towed (fun v=>envelope C m d k (Q v) i) S F B' α δ → 
            Towed (fun _:V=>(1:ℝ)) S F B' α (ε*g^p) := by
  filter_upwards [WilsonMixedTaggedMeasuredReserve.original R simple K d k h L p hk
    (div_pos ep cp) slow] with r buyer C b m B β
  obtain ⟨D,room,_,wallet⟩:=buyer
  refine ⟨D,room,?_⟩
  intro N mn per g i bi im V I de fi J Q qp cap card S F B' α δ dp bound bank
  have pos(v:V):0 < envelope C m d k (Q v) i :=
    mul_pos (rust_paid _).1 (grantw (totalpos (qp v) i))
  have gp:0 ≤ g:=by change 0 ≤ (Real.sqrt _)⁻¹; positivity
  apply WilsonMixedTaggedUnweight.original bank pos dp (mul_nonneg ep.le (pow_nonneg gp p))
  intro j U s _
  have all:=wallet N mn per i bi im Q qp cap s (card s)
  calc δ ≤ c*(β^((k+h)*L)*Real.exp (-(D:ℝ))) := bound
       _ ≤ c*(((ε/c)*g^p)*Poly.toll (fun v=>envelope C m d k (Q v) i) s) :=
         mul_le_mul_of_nonneg_left all cp.le
       _ = _ := by field_simp

end YM.Integration.WilsonMixedTaggedMeasuredBudget
