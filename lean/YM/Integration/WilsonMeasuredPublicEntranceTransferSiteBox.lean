import YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins
/-! A physical box at a fixed reporting age gives a finite set of absolute cover-site tuples before either regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferSiteBox
open Filter Function Set Finset Lattice Cells Extraction Spec RG Wilson Source PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}
local notation "C₀"=> R.family

def room (f:ℕ)(radius:ℝ):Finset (Fin n→ Cover):=
  let ell:ℤ:=⌈radius/(C₀).S.a f⌉
  Finset.Icc (fun _ _=> -ell) (fun _ _=>ell)

theorem inside {f:ℕ}{radius:ℝ}(o:Fin n→ Cover)
    (whereAt:∀i,‖(C₀).S.gridPoint f (o i)‖≤radius):o∈room R f radius:=by
  classical
  let ell:ℤ:=⌈radius/(C₀).S.a f⌉
  have axis(i:Fin n)(a:Axis):-ell≤o i a ∧ o i a≤ell:=by
    have coord:|(C₀).S.a f*(o i a:ℝ)|≤radius:=
      (PiLp.norm_apply_le ((C₀).S.gridPoint f (o i)) a).trans (whereAt i)
    rw [abs_mul,abs_of_pos ((C₀).S.a_pos f)] at coord
    have charge:|(o i a:ℝ)|≤ radius/(C₀).S.a f:=
      (le_div_iff₀ ((C₀).S.a_pos f)).mpr (by simpa only [mul_comm] using coord)
    have capped:|(o i a:ℝ)|≤(ell:ℝ):=charge.trans (Int.le_ceil _)
    exact_mod_cast abs_le.mp capped
  exact Finset.mem_Icc.mpr ⟨fun i a=>(axis i a).1,fun i a=>(axis i a).2⟩

end YM.Integration.WilsonMeasuredPublicEntranceTransferSiteBox
end
