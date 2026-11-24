import YM.Integration.WilsonMixedTaggedMeasuredWindow
import YM.Integration.WilsonMixedTaggedWindowBill

/-! The true crossLevel−2/first-stop interval spends one support exponent
and pays the full lower inverse radius uniformly at every held field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedMeasuredReserve
open Filter Finset Function Lattice Wilson RG Marker RG05Readout Many OPE
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G:Gauge}

theorem original (R:Run G) (simple:G.Simple) (K d k h L p:ℕ) (hk:0 < K) {ε:ℝ} (ep:0 < ε)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG05Readout.Lambda R.family.path.levels j)) :
    ∀ᶠ r in 𝓝[>] (0:ℝ),let C:=R.family
      let b:=crossLevel C.S r-1-1
      let m:=WilsonMeasuredWindow.stop C.path.levels simple K r
      let B:=(C.path.levels.budget m).B
      let β:=C.path.levels.clock.hatBeta m
      ∃ D:ℕ,D*(4*B+2)+2*B ≤ B^2 ∧ β^((k+h)*L)*Real.exp (-(D:ℝ)) ≤ 1 ∧ 
        ∀N:ℕ,m ≤ N → ∀per:ℕ,let g:=(Real.sqrt (C.path.rep N per m).beta)⁻¹
          ∀i:ℕ,b ≤ i → i ≤ m → ∀ {V:Type}[DecidableEq V]{J:Census V} (Q:V → ℝ),
            (∀v,0 < Q v) → (∀v,Q v ≤ β^h) → ∀s:J.Mode,s.val.card ≤ L → 
            β^((k+h)*L)*Real.exp (-(D:ℝ)) ≤ (ε*g^p)*
              Poly.toll (fun v=>envelope C m d k (Q v) i) s := by
  obtain ⟨dates,windows⟩:=WilsonMixedTaggedMeasuredWindow.original R simple K hk slow
  have prices:=dates.eventually (WilsonMixedTaggedWindowBill.original R simple (K+3) d k h L p ep)
  filter_upwards [prices,windows] with r bought geometry
  intro C b m B β
  obtain ⟨D,room,raw,all⟩:=bought
  exact ⟨D,room,raw,all b geometry.2.1 geometry.2.2⟩

end YM.Integration.WilsonMixedTaggedMeasuredReserve
