import YangMills.WilsonProof.NativeSupport.OriginalPattern
import YM.Next.FOUNDATIONS.Primary

/-! The physical source expense is purchased on the compact group before
choosing the original periods or the relative slot locations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson Next.Foundations Labels
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

def atomPrice (G : Gauge) (d : ℕ) : ℝ := (full_value_bound G d).choose
theorem atom_one (G : Gauge) (d : ℕ) : 1≤atomPrice G d := (full_value_bound G d).choose_spec.1

theorem atom_bound (d : ℕ) (i : ((frames G).level d).Index) (o : Site n) (U : Config G n) :
    ‖(localSection G d).places (Pi.single i 1) o U‖ ≤ atomPrice G d :=
  ((full_value_bound G d).choose_spec.2 i).2 n o U

theorem atom_local (d : ℕ) (i : ((frames G).level d).Index) (o : Site n) {s : ℕ}
    (radius : minSide G d ≤ s) : LocalOn (halo s {o}) ((localSection G d).places (Pi.single i 1) o) := by
  have cover : (localSection G d).footprint o ⊆ halo s {o} := by
    intro e he
    obtain ⟨v,hv,rfl⟩:=mem_image.mp he
    have is_box : v∈box s := by
      apply box_test.mpr
      have abs (j) : |v j| ≤ (s:ℤ) := by
        have c:=stencil_price G radius v hv j
        rw [←Int.natCast_natAbs]
        exact_mod_cast (show (v j).natAbs ≤ s by omega)
      exact ⟨fun j=>(abs_le.mp (abs j)).1,fun j=>(abs_le.mp (abs j)).2⟩
    exact halo_spec.mpr ⟨o,mem_singleton_self _,Work.E08.separation_box_add o is_box⟩
  intro U Z agree
  exact (localSection G d).placed_local o (Pi.single i 1) U Z
    (fun e h1 h2=>agree e (cover h1) (cover h2))

def component (b : Bool) : ℂ →L[ℝ] ℝ := if b then Complex.imCLM else Complex.reCLM

theorem component_norm (b : Bool) (z : ℂ) : |component b z| ≤ ‖z‖ := by
  cases b
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

def phase (b : Bool) : ℂ := if b then Complex.I else 1
theorem phase_norm (b : Bool) : ‖phase b‖=1 := by cases b <;> simp [phase]

theorem component_product {I : Type} [Fintype I] [DecidableEq I] (z : I → ℂ) (b : Bool) :
    component b (∏ i,z i)=∑ σ : I → Bool,component b (∏ i,phase (σ i))*(∏ i,component (σ i) (z i)) := by
  have term (i) : z i=∑ e:Bool,phase e*(component e (z i):ℂ) := by
    rw [Fintype.sum_bool]
    simp only [phase,component,ite_true,ite_false,Bool.false_eq_true,one_mul,
      Complex.reCLM_apply,Complex.imCLM_apply]
    rw [mul_comm Complex.I,add_comm,Complex.re_add_im]
  have expand : (∏ i,z i) = ∑ σ : I → Bool,(∏ i,component (σ i) (z i)) • (∏ i,phase (σ i)) := by
    calc _ = ∏ i,∑ e:Bool,phase e*(component e (z i):ℂ) := prod_congr rfl fun i _=>term i
         _ = ∑ σ : I→Bool,∏ i,phase (σ i)*(component (σ i) (z i):ℂ) := Fintype.prod_sum _
         _ = _ := by
            apply sum_congr rfl
            intro σ _
            rw [prod_mul_distrib,Complex.real_smul,Complex.ofReal_prod,mul_comm]
  rw [expand,map_sum]
  apply sum_congr rfl
  intro σ _
  rw [map_smul,smul_eq_mul,mul_comm]

end YM.Integration.InletSusceptibility.Packet
