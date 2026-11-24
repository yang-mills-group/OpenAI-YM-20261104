import YM.Integration.WilsonCoherentMayerPriorAtom
import YM.Integration.NativePaidPacketColors

/-! The true power stratum and its absolutely summed finite-degree radial readout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorStratum
open Lattice Wilson RG Marker Progress.DirectedRecipe Source Labels LocalComparison
open Comparison.Density.RenderM NativePaidPacketGroups WilsonMeasuredPathTaylor WilsonCoherentMayerPriorAtom
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge} {V:Type} [DecidableEq V] {n:Side} {Γ:Census V}
    {D:V→ ComparisonDensity.Address.Orbit} {P:MarkedPackets D G n Γ}
    {p:BudgetPoint} {ad:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width bank:ℝ} {off slope:ℕ}
    (H:P.Paid p ad region w g width bank off slope)

def rent (width:ℝ) {s:Γ.Mode}{z:ℤ} (i:Fiber P s z):ℝ:=
  (token P s z i).coin*Real.exp (width*(token P s z i).fall)

def weight (w:V→ℝ) (g:ℝ) (s:Γ.Mode) (z:ℤ):ℝ:=Poly.toll w s*‖(g:ℂ)^z‖

def row (P:MarkedPackets D G n Γ) (s:Γ.Mode)(z:ℤ)(x:TestSpace D)(a:Directions G n)(q:ℕ)(t:ℝ):ℂ:=
  ∑'i:Fiber P s z,print (token P s z i) x a q t

include H in
theorem positive (hg:g≠0) (s:Γ.Mode) (z:ℤ):0<weight w g s z:=
    mul_pos (Poly.worth H.positive s) (norm_pos_iff.mpr (zpow_ne_zero z (Complex.ofReal_ne_zero.mpr hg)))

include H in
theorem paid (hg:g≠0) (s:Γ.Mode) (hs:s.val.Nonempty) (z:ℤ):
    SumBudget (fun i:Fiber P s z=>rent width i) (bank/weight w g s z):=by
  obtain ⟨v,hv⟩:=hs
  have root:=Push.Local.sumBudget_subtype
    (fun i=>P.mode i=s ∧ P.power i=z ∧ (P.packet i).isSome) (H.roots v)
  have hL:=positive H hg s z
  have take:SumBudget (fun i:Fiber P s z=>weight w g s z*rent width i) bank:=by
    change SumBudget (fun i:Fiber P s z=>_) bank at root
    refine Push.Local.sumBudget_mono root ?_ ?_ le_rfl
    · intro i
      exact mul_nonneg hL.le (mul_nonneg (H.coefficient i.val _ (token_eq P s z i)).1
        (Real.exp_pos _).le)
    · intro i
      simp only [rent,weight,i.property.1,i.property.2.1,token_eq P s z i,if_pos hv]
      exact le_of_eq (by ring)
  have finish:=Push.Local.sumBudget_mul_left take (inv_nonneg.mpr hL.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hL.ne',one_mul,div_eq_inv_mul] using finish

include H in
theorem purchased (hg:g≠0) (s:Γ.Mode) (hs:s.val.Nonempty) (z:ℤ)
    (x:IndependentTests D)(a:Directions G n){A:ℝ}(ha:0≤A)(available:∀e,speed a e≤A)(q:ℕ)(t:ℝ):
    ‖NativePaidPacketSeries.value P s z (testInclusion D x) (field a t)-
      row P s z (testInclusion D x) a q t‖≤(2*fee width A q t)*(bank/weight w g s z):=by
  let u (i:Fiber P s z):=(token P s z i).read (testInclusion D x) (field a t)
  let printed (i:Fiber P s z):=print (token P s z i) (testInclusion D x) a q t
  let b:=2*fee width A q t
  have hb:0≤b:=by dsimp only [b,fee];have hw:=H.width_pos;positivity
  have cash:=paid H hg s hs z
  have fu:Summable u:=NativePaidPacketSeries.value_summable H hg s
    (fun he=>Finset.nonempty_iff_ne_empty.mp hs (by rw [he];rfl)) z (testInclusion D x) (field a t)
  have each (i:Fiber P s z):‖u i-printed i‖≤b*rent width i:=
    WilsonCoherentMayerPriorAtom.purchased H (token_eq P s z i) x a ha available q t
  have normed:=Summable.of_nonneg_of_le (fun i=>norm_nonneg (u i-printed i)) each (cash.2.1.mul_left b)
  have fp:Summable printed:=by simpa only [Pi.sub_apply,sub_sub_cancel] using fu.sub normed.of_norm
  change ‖(∑'i,u i)-(∑'i,printed i)‖≤b*(bank/weight w g s z)
  rw [←fu.tsum_sub fp]
  apply (norm_tsum_le_tsum_norm normed).trans ((normed.tsum_le_tsum each (cash.2.1.mul_left b)).trans ?_)
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left cash.2.2 hb

end YM.Integration.WilsonCoherentMayerPriorStratum
