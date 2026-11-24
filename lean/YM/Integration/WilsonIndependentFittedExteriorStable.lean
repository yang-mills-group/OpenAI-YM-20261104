import YM.Integration.WilsonIndependentFittedExteriorRung
import YM.Integration.WilsonOriginalPublicPlantedStableCredit

/-! The restored exterior takes its stable gain from its own two dated endpoints. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedExteriorStable
open Filter Lattice RG Wilson Source Labels Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonOriginalPublicPlantedStableCredit (age span)
open scoped Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Frame G h}{H:Hol G}{T:SectionData F}
    {p:h<D}{v:Rails h k u e}{E A K U:Credit}

theorem credit (C:Credit)(B η:ℝ)(positive:0<η):
    ∀ᶠ x:ℝ in atTop,∀L:CutsP H T p v E A K U,L.vesselsC.y L.m ≤ B →
      span L L.i=x → C.buy L.Age ≤ Real.exp (η*x):=by
  let b:=2+(Real.log 3)⁻¹
  have cp:0≤C.x:=zero_le_one.trans C.good
  have slow:Tendsto (fun x:ℝ=>x^C.d*Real.exp (-(η*x))) atTop (𝓝 0):=by
    simpa [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C.d:ℝ) η positive
  have vanish:Tendsto (fun x:ℝ=>C.x*b^C.d*(x^C.d*Real.exp (-(η*x)))) atTop (𝓝 0):=by
    simpa using slow.const_mul (C.x*b^C.d)
  filter_upwards [eventually_ge_atTop B,eventually_ge_atTop (0:ℝ),
    vanish.eventually_le_const (show (0:ℝ)<1 by norm_num)] with x big pos small L home atScale
  have yn:0≤L.Age:=by
    change 0≤L.vesselsC.y L.m+span L L.i+(L.i:ℝ)
    rw [atScale]
    linarith only [pos,L.vesselsC.depth L.m L.ha,Nat.cast_nonneg (α:=ℝ) L.i]
  have budget:L.Age≤b*x:=by
    have bill:=age L B home
    rw [atScale] at bill
    dsimp only [b]
    linarith only [bill,big]
  have paid:C.buy L.Age*Real.exp (-(η*x))≤1:=by
    calc _≤(C.x*(b*x)^C.d)*Real.exp (-(η*x)):=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ yn budget _) cp) (Real.exp_pos _).le
         _=C.x*b^C.d*(x^C.d*Real.exp (-(η*x))):=by rw [mul_pow];ring
         _≤1:=small
  have out:=mul_le_mul_of_nonneg_right paid (Real.exp_pos (η*x)).le
  rwa [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at out

theorem power (L:CutsP H T p v E A K U)(η:ℝ):
    Real.exp (η*span L L.i)=(L.ax.S.a L.ceilC/L.ax.S.a L.m)^(-η):=by
  rw [Real.rpow_def_of_pos (div_pos (L.ax.S.a_pos _) (L.ax.S.a_pos _)),
    Real.log_div (L.ax.S.a_pos _).ne' (L.ax.S.a_pos _).ne']
  unfold span Schedule.scale
  rw [Real.log_inv,Real.log_inv]
  congr 1
  ring

/-- Every lag, angular rank and retained moment is heard on the returned
cuts. The original scale compensation is restored exactly once. -/
theorem original (B η:ℝ)(positive:0<η):
    ∃cut:ℝ,∀(L:CutsP H T p v E A K U),L.vesselsC.y L.m ≤ B → cut ≤ span L L.i →
      ∀(a fee:ℝ),0<a→L.fuel=a*fee→∀lag≤e,∀i≤L.i,∀r:ℕ,∀moment≤u,
      Fruit 0 1 moment (((a⁻¹:ℝ) • L.springP i).2 lag r)
        ((L.ax.S.a L.ceilC/L.ax.S.a L.m)^(-η)*
          (L.ax.S.a L.ceilC/L.ax.S.a (L.m+i))^(1/4:ℝ)*fee):=by
  obtain ⟨C,paid⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E A K U
  obtain ⟨cut,gate⟩:=eventually_atTop.1 (credit (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (A:=A) (K:=K) (U:=U) C B η positive)
  refine ⟨cut,?_⟩
  intro L home length a fee warm actual lag hl i hi r moment hm
  have room:=gate _ length L home rfl
  rw [power] at room
  have fare:=((paid L).2.2 lag hl i hi r).slice zero_le_one hm
  have issued:=fare.μ a⁻¹
  rw [abs_of_pos (inv_pos.mpr warm),actual,WilsonIndependentFittedExteriorRung.gain] at issued
  have align (x:ℝ):a⁻¹*(C.buy L.Age*x*(a*fee))=C.buy L.Age*x*fee:=by field_simp
  rw [align] at issued
  have nn:0≤fee:=by
    have h₀:=L.hf
    rw [actual] at h₀
    exact nonneg_of_mul_nonneg_right h₀ warm
  apply issued.more
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right room
    (Real.rpow_nonneg (div_pos (L.ax.S.a_pos _) (L.ax.S.a_pos _)).le _)) nn

end YM.Integration.WilsonIndependentFittedExteriorStable
