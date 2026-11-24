import YM.Integration.WilsonOriginalMicroscopicEntranceGridPeer

/-! Finite masked sibling products are summed on the actual single f-level
posterior, including its normalization at an arbitrary earlier field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceCropFields
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent Marker
open WilsonOriginalMicroscopicEntranceGridRow (factor signed)
open WilsonThermometerUnitFilingCoarse (reading)
open private summed from YM.Integration.WilsonThermometerOccupiedLinear
open WilsonOriginalMicroscopicEntranceGridPeer (held)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f u:ℕ}
local notation "C₀" => R.family
local notation "P" => R.family.path.rep N p f
local notation "X" i:max => Config G (R.family.side i p)


theorem numerator (live:f≤N)(a:Fin 3)(o:Site ((C₀).side f p))(z:store C₀ (d a) p f)
    (E:X f→ℂ)(B:ℝ)(source:X f→ℂ)(filed:WilsonAddressedRestartedFiled.Filed R (d a) N p f o source B z):
    (fun U=>(P).eval U • (signed R d (N:=N) a o z U*E U))=
      (-(WilsonOriginalMicroscopicEntranceGridRow.factor R d f a)) • (fun U=>source (Lattice.translate o U)*E U):=by
  funext U
  have ne:((P).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
  have af:(R.family.S.a f:ℂ)≠0:=by exact_mod_cast (R.family.S.a_pos f).ne'
  simp only [signed,Complex.real_smul,Pi.smul_apply,smul_eq_mul,WilsonOriginalMicroscopicEntranceGridRow.factor,
    filed.field,Function.comp_apply]
  field_simp [ne,af]

theorem original (live:f≤N)(o:Fin 3→Site ((C₀).side f p))(z:∀a:Fin 3,store C₀ (d a) p f)
    (E:Fin 3→X f→ℂ)(B:Fin 3→ℝ)(source:Fin 3→X f→ℂ)
    (filed:∀a,WilsonAddressedRestartedFiled.Filed R (d a) N p f (o a) (source a) (B a) (z a))
    (bill:∀a,Integrable (fun U=>source a (Lattice.translate (o a) U)*E a U) (prior G _))(uf:u≤f)(W:X u):
    let crop:=fun a (U:X f)=>signed R d (N:=N) a (o a) (z a) U*E a U
    Integrable (fun U=>(P).eval U • ∑a:Fin 3,crop a U) (prior G _) ∧
       actualTransport C₀ (N:=N) (fun U=>∑a:Fin 3,crop a U) uf W=
         ∑a:Fin 3,actualTransport C₀ (N:=N) (crop a) uf W:=by
  intro crop
  let coeff:=fun a=> -(WilsonOriginalMicroscopicEntranceGridRow.factor R d f a)
  let row:=fun a (U:X f)=>source a (Lattice.translate (o a) U)*E a U
  have collect:(fun U=>(P).eval U • ∑a:Fin 3,crop a U)=∑a:Fin 3,coeff a • row a:=by
    funext U
    simp only [Finset.smul_sum,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    exact congrFun (numerator R d live a (o a) (z a) (E a) (B a) (source a) (filed a)) U
  have receipt:=summed R (N:=N) Finset.univ coeff row bill uf
  refine ⟨collect ▸ receipt.1,?_⟩
  calc
    actualTransport C₀ (N:=N) (fun U=>∑a:Fin 3,crop a U) uf W=
       ∑a:Fin 3,coeff a*WilsonOriginalMicroscopicEntranceGridPeer.held R (N:=N) (row a) uf W:=by
      unfold actualTransport WilsonOriginalMicroscopicEntranceGridPeer.held
      rw [collect,receipt.2]
      simp only [Finset.sum_apply,Pi.smul_apply,Finset.smul_sum,Complex.real_smul,smul_eq_mul,
        Complex.ofReal_inv]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _:=by
      apply Finset.sum_congr rfl
      intro a _
      exact (WilsonOriginalMicroscopicEntranceGridPeer.original R d live a (o a) (z a) (E a) (B a) (source a) (filed a) (bill a) uf W).symm

end YM.Integration.WilsonOriginalMicroscopicEntranceCropFields
end
