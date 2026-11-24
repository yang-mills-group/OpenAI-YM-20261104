import YM.Integration.WilsonCoherentMayerPriorCoefficient
import YM.Integration.WilsonCoherentMayerPriorPowers

/-! The measured-source polynomial is the Taylor polynomial of the complete normalized incoming finite file. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorDiagonal
open Lattice Wilson RG Exterior Marker LocalComparison Precision NativePaidPacketColors
open Comparison.RG02 Comparison.RG02.Assembly Comparison.Density.RenderM Next.SectorChange.Flat
open WilsonMeasuredPathTaylor WilsonCoherentMayerPriorDifferential WilsonCoherentMayerPriorCoefficient
open WilsonCoherentMayerPriorStratum WilsonCoherentMayerPriorAtom
open scoped Classical BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {n:Side} {Γ:Census V}
    {D:V→ ComparisonDensity.Address.Orbit} {P:MarkedPackets D G n Γ}
    {p:BudgetPoint} {ad:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width bank:ℝ} {off slope:ℕ}
    (H:P.Paid p ad region w g width bank off slope)

def drawn (P:MarkedPackets D G n Γ)(s:Γ.Mode)(x:TestSpace D)(a:Directions G n)(K:ℕ)(t:ℝ):ℂ:=
  ∑z∈powers P,(t:ℂ)^z*WilsonMeasuredPathTaylor.jet (reading P s z x a) ((K:ℤ)-z).toNat t

def file (E:ℝ→fieldDir G n 1→Poly Γ)(s:Γ.Mode)(B:fieldDir G n 1)(K:ℕ)(t:ℝ):ℂ:=
  ∑k∈Finset.range (K+1),(t:ℂ)^k*
    ((((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k (fun u=>E u B) 0 (fun _=>1)):Poly Γ).part s

include H in
theorem exact_file (hg:g≠0)(s:Γ.Mode)(hs:s≠Γ.quiet)(x:TestSpace D)(a:Directions G n)(K:ℕ)
    (cap:P.powerCap≤K)(t:ℝ)(ht:t≠0)(E:ℝ→fieldDir G n 1→Poly Γ)
    (value:∀t:ℝ,t≠0→∀A,E t A=P.read x t (represent (t•A)))
    (live:∀A,ContinuousAt (fun u=>E u A) 0)(smooth:ContDiffAt ℝ K (fun u=>E u (labels a)) 0):
    drawn P s x a K t=file E s (labels a) K t:=by
  unfold drawn file
  have table(k:ℕ)(hk:k∈Finset.range (K+1)):
      ∑z∈powers P,layer P x s k z (labels a)=
        ((((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k (fun u=>E u (labels a)) 0 (fun _=>1)):Poly Γ).part s:=
    (WilsonCoherentMayerPriorCoefficient.filed H hg x s hs k (labels a) E value live
      (smooth.of_le (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)))).symm
  calc
    _=∑z∈powers P,∑k∈Finset.range (K+1),(t:ℂ)^k*layer P x s k z (labels a):=by
      apply Finset.sum_congr rfl
      intro z hz
      let b(j:ℕ):=Assembly.jet (stratum P x s z) j (labels a)
      have vanish(j:ℕ)(hj:j<(-z).toNat):b j=0:=(NativePaidPacketSeries.value_grade H hg s hs z x).jet_z (labels a) hj
      have upper:z≤(K:ℤ):=le_trans (Finset.mem_Icc.mp hz).2 (by exact_mod_cast cap)
      have thermal:=WilsonCoherentMayerPriorPowers.assemble z K upper b vanish (t:ℂ) (by exact_mod_cast ht)
      refine Eq.trans ?_ thermal
      apply congrArg ((t:ℂ)^z*·)
      unfold WilsonMeasuredPathTaylor.jet
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm (↑j.factorial:ℝ)⁻¹ (t^j),mul_smul,WilsonCoherentMayerPriorCoefficient.radial H hg x s hs z a j]
      change ((t^j:ℝ):ℂ)*b j=(t:ℂ)^j*b j
      rw [Complex.ofReal_pow]
    _=∑k∈Finset.range (K+1),(t:ℂ)^k*(∑z∈powers P,layer P x s k z (labels a)):=by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _=_:=Finset.sum_congr rfl fun k hk=>congrArg ((t:ℂ)^k*·) (table k hk)

end YM.Integration.WilsonCoherentMayerPriorDiagonal
