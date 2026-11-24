import YM.Integration.WilsonMeasuredPublicEntranceCanonicalEar
import YM.Integration.WilsonSeparatedPrefixCanonicalClearWithdrawal
import YM.Integration.WilsonOriginalAlternativeHearing
/-! A single deposited hard owner on the original physical Wilson host with
a finite family of masked peers at an arbitrary earlier clear field. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCanonicalClearEar
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open WilsonMeasuredCoefficientTransport WilsonMeasuredPublicEntranceOwnerGas
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open WilsonSeparatedPrefixCanonicalClearConvolution
open private linear from YM.Integration.WilsonOriginalAlternativeHearing
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "S₂" => Marks (V×Bool)
local notation "V₂" => V×Bool
local notation "X" => Unit×(V×Bool)

theorem original (simple:G.Simple)(cater:Cater (C) R.doors)
:
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j≤k+1) (_kn:k<N)
      (o:V → Site ((C).side (k+1) p))(w₀ w:V → ℝ)(route:∀t,X → Site ((C).side t p)),
    let P:=(C).path.rep N p (k+1)
    let e:=P.p.supportExponent-1
    let μ:=fun i=>w i^2
    let W:=w ∘ Prod.fst (β:=Bool)
    let κ:=LocalComparison.forcedDivisor (C) (k+1)
    ∀(owner:V)(d:ℕ)(q:Coefficient ((C).labels.level d) ((C).side (k+1) p))(B:ℝ)
      (φ:V → Config G ((C).side (k+1) p) → ℂ)
      (M:V → Support ((C).side (k+1) p) → Config G ((C).side (k+1) p) → Poly S₀)
      (c:V → Poly S₀)(m cap:V → ℝ),
    (∃ (x:V → Config G ((C).side (k+1) p) → ℂ), ∃ h, ∃ F:Config G ((C).side (k+1) p) → Poly S₀,Served P x h F o w₀ P.p.supportExponent 1) →
    (∀v,0<w₀ v) → (∀v,0<w v) → (∀v,μ v≤w₀ v) → 0≤P.p.supportExponent → 5≤P.p.B →
    (∀a b:V,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    q.Format (o owner) (C).params P → q.remBound (o owner) P κ B → μ owner*B≤1/2 →
    (∀v Z,Burns o Z (M v Z) P.p.threshold) →
    (∀v,Towed μ id (M v) P.p.B e (m v)) → (∑v,m v)+1/4≤1 →
    (∀v,(c v).part (S₀).quiet=0) → (∀v,Poly.price μ (c v)≤cap v) →
    (∀v U,Poly.send ((S₀).fire v) (φ v U)=c v+∑Z,M v Z U) →
    route (k+1)=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    2≤((A).budget j).supportExponent → ∀U:Config G ((C).side j p),
    flags ((C).path.rep N p j).p.threshold U=∅ →
    ∀s:(S₀).Mode,owner∈s.val → Poly.toll μ s*
      ‖readingAt R (N:=N) (fun H=>account q P H*(∏i∈s.val.erase owner,φ i H)) height U‖≤
      Real.exp (∑v,cap v)*((WilsonSeparatedPrefixCanonicalTapRate.value R (k+1))⁻¹*
        WilsonOriginalOccupiedStencil.price (Fintype.card V₂))*
      (∑t:(S₂).Mode,Poly.toll W t*WilsonSeparatedPrefixCanonicalClearHeard.roof R W t (k+1) j):=by
  obtain ⟨j₀,taps⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalTapRate.original R simple (Fintype.card V₂))
  filter_upwards [WilsonSeparatedPrefixCanonicalClearWithdrawal.original (V:=V) R simple cater,
    eventually_ge_atTop j₀] with j receiver late N p k height kn o w₀ w route P e μ W κ owner d q B φ M c m cap sale p₀ wp within exponent wide apart fit fare narrow loc fees soft quiet constants split course parent old
  classical
  obtain ⟨_,_,_,actual⟩:=sale
  let h:=selected P q owner
  let F:=restore (B:=S₀) P φ h 0 0
  let r:=fun i=>if i=owner then μ owner*(κ*B) else 0
  let E:=WilsonSeparatedPrefixCanonicalTapRate.value R (k+1)
  let T:ℂ:=E
  have pos:0<E:=Real.exp_pos _
  have large:1≤E:=Real.one_le_exp (div_nonneg (sq_nonneg _) (by norm_num))
  have low:‖T⁻¹‖=E⁻¹:=by rw [norm_inv];congr 1;exact Complex.norm_real _ |>.trans (Real.norm_of_nonneg pos.le)
  have small:‖T⁻¹‖≤1:=by rw [low];exact inv_le_one_of_one_le₀ large
  have inverse:T*T⁻¹=1:=mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr pos.ne')
  have base:P.p=(A).budget (k+1):=(R.makes.wilson.represents N p (k+1) (by omega)).vac
  have mp:∀i,0<μ i:=fun i=>sq_pos_of_pos (wp i)
  have keys:=WilsonMeasuredPublicEntranceOwnerFlags.original (J:=S₀) o q owner μ mp exponent
    (show e≤P.p.supportExponent by dsimp [e];linarith) fit fare
  have paid(z:ℂ)(hz:z∈nodes (Fintype.card V₂) T):
      4*‖z‖≤Real.exp ((P.p.B/8:ℕ):ℝ) ∧ (∑i,‖z‖*r i)+1/4≤1:=by
    have scheduled:=taps (k+1) (by omega) z hz
    refine ⟨base.symm ▸ scheduled.1,?_⟩
    have sum:(∑i,‖z‖*r i)=(‖z‖*κ)*(μ owner*B):=by
      simp only [r,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true];ring
    rw [sum]
    have cash:=mul_le_mul scheduled.2 narrow (mul_nonneg (mp _).le (rem_nonneg fare)) zero_le_one
    linarith
  have stock:Served P φ h F o w₀ ((((A).budget (k+1)).supportExponent-1)+1) 1:=by
    simpa only [←base,sub_add_cancel] using WilsonMeasuredPublicEntranceOwnerSale.stocked P φ q owner p₀ actual
  have valid:=(R.makes.wilson.represents N p (k+1) (by omega)).good.labels
  have backed:=receiver N p k height kn o w₀ w route φ h F M c m r cap T T⁻¹ stock p₀ wp within wide apart loc (fun i=>(keys i).2)
    (by simpa only [←base] using fees) (by simpa only [←base] using (fun i=>(keys i).1)) soft quiet constants split inverse small paid ⟨_,_,valid⟩ course parent old
  intro endpoint clear s inside
  have out:=backed endpoint clear s
  have regular:=WilsonMeasuredPublicEntranceOwnerIntegrable.local_rows R o φ c M μ loc fees split
  have integr:=WilsonMeasuredPublicEntranceOwnerIntegrable.together R (by omega:k+1≤N) φ regular q (o owner) fit fare s inside
  have row(U): (F U).part s-(P.eval U:ℂ)*(∏v∈s.val,φ v U)=account q P U*(∏i∈s.val.erase owner,φ i U):=
    WilsonMeasuredPublicEntranceOwnerSale.fieldwise P φ q owner valid fare s inside U
  let F₁:=fun U=>(F U).part s
  let F₀:=fun U=>(P.eval U:ℂ)*(∏v∈s.val,φ v U)
  have reduced:=congrFun (linear (C) N p height F₁ F₀ integr.1 integr.2) endpoint
  simp only [Pi.sub_apply] at reduced
  rw [←funext row]
  unfold readingAt at out ⊢
  rw [low,←mul_sub] at out
  exact reduced.symm ▸ out

end YM.Integration.WilsonMeasuredPublicEntranceCanonicalClearEar
end
