import YM.Integration.WilsonPositionScaleLawContinuum
import YM.Integration.WilsonPositionScaleLawOneFee

/-! Uniform continuous-length bounds for the original homogeneous fixed-field
columns from the one first-order same-home quadratically bounded survey at a
single dyadic ratio. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawSingleGrade
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawFixed (top normalized)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawKinetic (kinetic)
open private cap from YM.Integration.WilsonPositionScaleLawTrajectory
open scoped Topology Classical Asymptotics

theorem bilateral {X Y:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X]
    (A:ℕ→X→L[ℂ]X)(z:ℕ→Y→X)(K:ℝ)(hK:0≤K)
    (fee:∀ᶠn:ℕ in atTop,‖A n-ContinuousLinearMap.id ℂ X‖≤K/((n:ℝ)+1))
    (relation:∀ᶠn:ℕ in atTop,∀O:Y,z n O=A n (z (n+1) O)):
    ∃N p:ℕ,∀k:ℕ,∀O:Y,
      let ratio:=(((N+k:ℕ):ℝ)+1)^p/((N:ℝ)+1)^p
      ‖z (N+k) O‖≤ratio*‖z N O‖ ∧ ‖z N O‖≤ratio*‖z (N+k) O‖:=by
  obtain ⟨L,_,back⟩:=WilsonPositionScaleLawIteration.backward A K hK fee
  obtain ⟨N,after⟩:=eventually_atTop.mp ((fee.and back).and relation)
  obtain ⟨p,large⟩:=exists_nat_ge (max K L)
  have pk:K≤p:=(le_max_left ..).trans large
  have pl:L≤p:=(le_max_right ..).trans large
  let scale(k:ℕ):ℝ:=(((N+k:ℕ):ℝ)+1)^p/((N:ℝ)+1)^p
  refine ⟨N,p,?_⟩
  intro k O
  change ‖z (N+k) O‖≤ scale k*‖z N O‖ ∧ ‖z N O‖≤ scale k*‖z (N+k) O‖
  induction k with
  | zero=>simp [scale,div_self (show ((N:ℝ)+1)^p≠0 by positivity)]
  | succ k ih=>
    let n:=N+k
    let h:ℝ:=(n:ℝ)+1
    let w:=((h+1)/h)^p
    have hh:0<h:=by dsimp [h];positivity
    have hw:0≤w:=by dsimp [w];positivity
    have hs:0≤ scale k:=by dsimp [scale];positivity
    obtain ⟨⟨out,inv,inn⟩,recur⟩:=after n (Nat.le_add_right ..)
    have eq:z n O=A n (z (n+1) O):=recur O
    have next:z (n+1) O=(A n).inverse (z n O):=by rw [eq,inv.inverse_apply_self]
    have forward:‖z (n+1) O‖≤w*‖z n O‖:=next ▸ cap _ L h p hh pl inn _
    have reverse:‖z n O‖≤w*‖z (n+1) O‖:=by calc
      _=‖A n (z (n+1) O)‖:=congrArg norm (recur O)
      _≤_:=cap _ K h p hh pk out _
    have multiply:w*scale k=scale (k+1):=by
      have hn:(((N+(k+1):ℕ):ℝ)+1)=h+1:=by dsimp [h,n];push_cast;ring
      dsimp only [scale,w]; rw [hn,div_pow];change (h+1)^p/h^p*(h^p/_)=_;field_simp
    constructor
    · exact forward.trans ((mul_le_mul_of_nonneg_left ih.1 hw).trans_eq (by rw [←mul_assoc,multiply]))
    · exact ih.2.trans ((mul_le_mul_of_nonneg_left reverse hs).trans_eq (by rw [←mul_assoc,mul_comm (scale k) w,multiply];rfl))

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (d:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d)(r:ℝ)(hr:0<r)
    (earned:WilsonPositionScaleLawOneFee.Earned Z M ν F J d r)(funded:Coupling G (kinetic Z F J))

include H lead paid raw hr earned funded in
theorem original:WilsonPositionScaleLawContinuum.Controlled Z F J d r:=by
  obtain ⟨K,hK,fee⟩:=WilsonPositionScaleLawOneFee.cost Z M H ν F J lead paid (top d) raw r hr earned funded
  obtain ⟨N,p,bound⟩:=bilateral _ _ K hK fee (WilsonPositionScaleLawFixed.balance F J Z lead d r hr)
  apply WilsonPositionScaleLawContinuum.fromDyadic Z M H F J lead d raw r hr
  refine ⟨N,p,?_⟩
  intro k O
  simp only [WilsonPositionScaleLawHomogeneous.identifies Z F J (WilsonPositionHomogeneousCoefficients.purchased Z H)]
  exact bound k O

end YM.Integration.WilsonPositionScaleLawSingleGrade
end
