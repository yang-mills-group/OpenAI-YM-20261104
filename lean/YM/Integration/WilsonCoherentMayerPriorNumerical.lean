import YM.Integration.WilsonCoherentMayerPriorDiagonal

/-! Finite total thermal order on the original signed packet and its measured power budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorNumerical
open Function Lattice Wilson RG Exterior Marker Precision LocalComparison NativePaidPacketColors WilsonMeasuredPathTaylor
open WilsonCoherentMayerPriorStratum WilsonCoherentMayerPriorAtom
open WilsonCoherentMayerPriorDiagonal WilsonCoherentMayerPriorDifferential Comparison.Density.RenderM Next.SectorChange.Flat
open scoped Classical BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G:Gauge} {V:Type} [DecidableEq V] {n:Side} {Γ:Census V}
    {D:V→ ComparisonDensity.Address.Orbit} {P:MarkedPackets D G n Γ}
    {p:BudgetPoint} {ad:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width bank:ℝ} {off slope:ℕ}
    (H:P.Paid p ad region w g width bank off slope)

include H in
theorem purchased [Fintype V] (hg:g≠0)(s:Γ.Mode)(hs:s.val.Nonempty)(x:IndependentTests D)(a:Directions G n)
    {A:ℝ}(ha:0≤A)(available:∀e,speed a e≤A)(q ord:ℕ)(hord:q+P.powerCap≤ord)
    (small:2*A*|g|/width≤1)(E:ℝ→fieldDir G n 1→Poly Γ)
    (value:∀u:ℝ,u≠0→∀B,E u B=P.read (testInclusion D x) u (represent (u•B)))
    (live:∀B,ContinuousAt (fun u=>E u B) 0)(smooth:ContDiffAt ℝ ord (fun u=>E u (labels a)) 0):
    Poly.toll w s*‖(P.read (testInclusion D x) g (field a g)).part s-
      file E s (labels a) ord g‖≤((powers P).card:ℝ)*(fee width A q g*bank):=by
  have hw:=H.width_pos
  have wallet:=Poly.worth H.positive s
  have nonnegative:0≤2*A*|g|/width:=by positivity
  have funded:0≤bank:=by
    obtain ⟨v,_⟩:=hs
    exact (tsum_nonneg (H.roots v).1).trans (H.roots v).2.2
  have nonempty:s≠Γ.quiet:=fun he=>Finset.nonempty_iff_ne_empty.mp hs (by rw [he];rfl)
  rw [←WilsonCoherentMayerPriorDiagonal.exact_file H hg s nonempty (testInclusion D x) a ord (by omega) g hg E value live smooth]
  rw [NativePaidPacketColors.read_mode_sum H hg s nonempty,drawn,←Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) wallet.le).trans
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑_z∈powers P,fee width A q g*bank:=by
      apply Finset.sum_le_sum
      intro z hz
      have upper:z≤(P.powerCap:ℤ):=(Finset.mem_Icc.mp hz).2
      have zfee:fee width A ((ord:ℤ)-z).toNat g≤fee width A q g:=
        pow_le_pow_of_le_one nonnegative small (by omega)
      have h:=WilsonCoherentMayerPriorJet.purchased H hg s hs z x a ha available ((ord:ℤ)-z).toNat g
      have wz:=positive H hg s z
      rw [←mul_sub,norm_mul,←mul_assoc]
      change weight w g s z * _ ≤ _
      calc
        _ ≤ weight w g s z*((fee width A ((ord:ℤ)-z).toNat g)*(bank/weight w g s z)):=
          mul_le_mul_of_nonneg_left h wz.le
        _ = fee width A ((ord:ℤ)-z).toNat g*bank:=by field_simp
        _ ≤ _:=mul_le_mul_of_nonneg_right zfee funded
    _ = _:=by simp [nsmul_eq_mul]

end YM.Integration.WilsonCoherentMayerPriorNumerical
