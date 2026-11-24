import YM.Integration.WilsonPositionScaleLawFixed

/-! The highest-grade component of a single fixed physical infrared field has
a two-sided polynomial growth estimate at the true dyadic radii, uniform in the
physical field. Both directions concern that very field at the two endpoints. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawTrajectory
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (sweep)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawQinter (measured)
open WilsonPositionScaleLawFixed (top normalized)
open private gain from YM.Integration.WilsonPositionScaleLawIteration
open scoped Topology Classical Asymptotics

private theorem cap {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X](A:X→L[ℂ]X)(K h:ℝ)(p:ℕ)
    (hh:0<h)(hp:K≤p)(fee:‖A-ContinuousLinearMap.id ℂ X‖≤K/h)(v:X):‖A v‖≤((h+1)/h)^p*‖v‖:=by
  let D:=A-ContinuousLinearMap.id ℂ X
  have eq:A v=v+D v:=by change _=v+(A v-v);abel
  calc
    _≤‖v‖+‖D v‖:=eq ▸ norm_add_le _ _
    _≤(1+K/h)*‖v‖:=by rw [add_mul,one_mul];exact add_le_add le_rfl ((D.le_opNorm v).trans (mul_le_mul_of_nonneg_right fee (norm_nonneg _)))
    _≤_:=mul_le_mul_of_nonneg_right (gain K h hh p hp) (norm_nonneg _)

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (d:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d)
    (observed:(measured Z M ν F J d 2)=o[sweep] (fun z=>kinetic Z F J z.1^2))
    (funded:Coupling G (kinetic Z F J))(r:ℝ)(hr:0<r)

include H lead paid raw observed funded hr in
theorem original :∃N p:ℕ,∀k:ℕ,∀O:S.Field d,
    let ratio:=(((N+k:ℕ):ℝ)+1)^p/((N:ℝ)+1)^p
    ‖normalized F J Z d r (N+k) O‖≤ratio*‖normalized F J Z d r N O‖ ∧
    ‖normalized F J Z d r N O‖≤ratio*‖normalized F J Z d r (N+k) O‖:=by
  let A:=WilsonPositionScaleLawDyadic.step Z F J (top d) r
  let z:=normalized F J Z d r
  obtain ⟨K,hK,fee⟩:=WilsonPositionScaleLawDyadic.cost Z M H ν F J lead paid (top d) raw observed funded r hr
  obtain ⟨L,_,back⟩:=WilsonPositionScaleLawIteration.backward A K hK fee
  obtain ⟨N,after⟩:=eventually_atTop.mp ((fee.and back).and (WilsonPositionScaleLawFixed.balance F J Z lead d r hr))
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

end YM.Integration.WilsonPositionScaleLawTrajectory
end
