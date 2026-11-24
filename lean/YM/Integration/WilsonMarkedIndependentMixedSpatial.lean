import YM.Integration.WilsonMarkedIndependentMixedOpening

/-! Recover a genuine spatial MarkU income from the cutoff-uniform signed
finite tensor error on the original compact occupied roster. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedSpatial
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι α V:Type}{n:Side}{r:ℕ}

theorem diameter (q:ι → Cover)(I:Finset ι)(x:dock (Site n) α r):
    Syn (tor n) (wrap n ∘ q) I x≤4*n.val:=by
  apply league_le
  intro i j
  exact crowd _

theorem restore [NormedAddCommGroup V][CompleteSpace V][Fintype α]
    {P:Ten V (Site n × α) r}{F:Ten V (Cloth α) r}{q:ι → Cover}{I:Finset ι}
    {s z A B:ℝ}(ready:I.Nonempty)(width:0<s)(pos:0<z)(price:0≤B)
    (income:Wig Bank.terrain q s A I F)
    (change:∀x,‖P x-plume F n x‖≤B*Real.exp (-(n.val:ℝ)/(4096*z))):
    MarkU q I P F (min (s/32) (1/(16384*z)))
      ((priceM α r s+tiePay α r (s/4)+1)*A+B):=by
  let v:=min (s/32) (1/(16384*z))
  have vp:0<v:=lt_min (by positivity) (by positivity)
  have base:MarkU q I (plume F n) F v ((priceM α r s+tiePay α r (s/4)+1)*A):=
    (plumeW income ready width).mono (min_le_left ..)
  have four:4*v≤1/(4096*z):=calc
    _≤4*(1/(16384*z)):=mul_le_mul_of_nonneg_left (min_le_right ..) (by norm_num)
    _=_:=by field_simp;ring
  have power (y:ℝ)(cap:y≤4*n.val):-(n.val:ℝ)/(4096*z)≤ -v*y:=by
    have lift:=mul_le_mul_of_nonneg_right four (Nat.cast_nonneg (α:=ℝ) n.val)
    have bound:=mul_le_mul_of_nonneg_left cap vp.le
    calc _=-(1/(4096*z)*(n.val:ℝ)):=by ring
         _≤-(4*v*(n.val:ℝ)):=neg_le_neg lift
         _≤_:=by linarith
  have δ:MarkU q I (P-plume F n) 0 v B:=by
    refine ⟨Wig.zero.more price,⟨price,?_⟩,⟨price,?_⟩⟩
    · intro x
      have size:((Syn (tor n) (wrap n ∘ q) I x:ℕ):ℝ)≤4*n.val:=by exact_mod_cast diameter q I x
      exact (change x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (power _ size)) price)
    · intro x _
      simp only [Pi.zero_apply,sub_zero,Pi.sub_apply]
      exact (change _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (power _ (by linarith [Nat.cast_nonneg (α:=ℝ) n.val] : (n.val:ℝ)≤4*n.val))) price)
  simpa only [add_sub_cancel,add_zero] using base.add δ

end YM.Integration.WilsonMarkedIndependentMixedSpatial
end
