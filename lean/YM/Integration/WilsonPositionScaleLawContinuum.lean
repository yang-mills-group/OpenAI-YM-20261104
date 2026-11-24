import YM.Integration.WilsonPositionScaleLawHomogeneous
import YM.Integration.WilsonPositionScaleLawEndpoint

/-! Extend the two-sided top-grade estimate for one fixed original field to
every sufficiently small physical length, with a logarithmic age fixed by the
actual continuous radius. The same exact homogeneous position frame is used. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawContinuum
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawHomogeneous (column)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawQinter (measured)
open scoped Topology Classical Asymptotics

theorem band (r:ℝ)(hr:0<r)(M:ℕ)(y:ℝ)(hy:0<y)(cut:y≤radius r M):
    ∃n:ℕ,M≤n ∧ ∃t:Ratio,t.val*radius r n=y ∧ (n:ℝ)≤Real.log (r/y)/Real.log 2:=by
  let u:ℝ:=1/2
  have hu:0<u:=by norm_num [u]
  have hu1:u<1:=by norm_num [u]
  have lim:y≤r:=cut.trans (by change r*u^M≤r;exact mul_le_of_le_one_right hr.le (pow_le_one₀ hu.le hu1.le))
  obtain ⟨n,lo,hi⟩:=exists_nat_pow_near_of_lt_one (div_pos hy hr) ((div_le_one hr).mpr lim) hu hu1
  have p:radius r (n+1)<y:=by simpa only [radius,mul_comm, u] using (lt_div_iff₀ hr).mp lo
  have q:y≤radius r n:=by simpa only [radius,mul_comm, u] using (div_le_iff₀ hr).mp hi
  have hn:M≤n:=by
    by_contra! against
    have higher:u^M≤u^(n+1):=pow_le_pow_of_le_one hu.le hu1.le against
    exact p.not_ge (cut.trans (mul_le_mul_of_nonneg_left higher hr.le))
  have rn:0<radius r n:=mul_pos hr (pow_pos hu _)
  have ht:y/radius r n∈Icc (1/2:ℝ) 1:=by
    refine ⟨(le_div_iff₀ rn).mpr ?_,(div_le_one rn).mpr q⟩
    apply le_trans _ p.le
    dsimp [radius];rw [pow_succ];ring_nf;exact le_rfl
  refine ⟨n,hn,⟨_,ht⟩,div_mul_cancel₀ y rn.ne',?_⟩
  have log:=WilsonPositionScaleLawClock.logRadius r hr n
  change Real.log ((radius r n)⁻¹)=(n:ℝ)*Real.log 2-Real.log r at log
  rw [Real.log_inv] at log
  apply (le_div_iff₀ (Real.log_pos (by norm_num:1<(2:ℝ)))).mpr
  rw [Real.log_div hr.ne' hy.ne']
  linarith [Real.log_le_log hy q]

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (d:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d)
    (observed:(measured Z M ν F J d 2)=o[sweep] (fun z=>kinetic Z F J z.1^2))
    (funded:Coupling G (kinetic Z F J))(r:ℝ)(hr:0<r)

def Dyadic:Prop:=∃N p:ℕ,∀k:ℕ,∀O:S.Field d,
    let ratio:=(((N+k:ℕ):ℝ)+1)^p/((N:ℝ)+1)^p
    ‖column Z F J d (radius r (N+k)) O‖≤ratio*‖column Z F J d (radius r N) O‖ ∧
    ‖column Z F J d (radius r N) O‖≤ratio*‖column Z F J d (radius r (N+k)) O‖

def Controlled:Prop:=∃N p:ℕ,∃ρ:ℝ,0<ρ ∧ ∀y:ℝ,0<y→y≤ρ→∀O:S.Field d,
    let price:=2*((Real.log (r/y)/Real.log 2+1)^p/((N:ℝ)+1)^p)
    ‖column Z F J d y O‖≤price*‖column Z F J d (radius r N) O‖ ∧
    ‖column Z F J d (radius r N) O‖≤price*‖column Z F J d y O‖

include H lead raw hr in
theorem fromDyadic (issued:Dyadic Z F J d r):Controlled Z F J d r:=by
  let C:=column Z F J d
  let CP:=WilsonPositionScaleLawEndpoint.column F J Z d
  have eq (a:ℝ)(O:S.Field d):C a O=CP a O:=congrArg ((a:ℂ)^d • ·)
    (WilsonPositionScaleLawHomogeneous.invariant Z F J (WilsonPositionHomogeneousCoefficients.purchased Z H) d a O)
  obtain ⟨N,p,dyadic⟩:=issued
  obtain ⟨l,after⟩:=eventually_atTop.mp ((WilsonPositionScaleLawClock.falls r hr).eventually (WilsonPositionScaleLawEndpoint.original F J Z lead d raw))
  refine ⟨N,p,radius r (N+l),mul_pos hr (pow_pos (by norm_num) _),?_⟩
  intro y hy small O
  obtain ⟨n,hn,t,loc,age⟩:=band r hr (N+l) y hy small
  have nl:l≤n:=by omega
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le (show N≤n by omega)
  have ep:=after n nl t O
  change ‖CP (t.val*radius r n) O‖≤2*‖CP (radius r n) O‖ ∧ ‖CP (radius r n) O‖≤2*‖CP (t.val*radius r n) O‖ at ep
  rw [loc,←eq,←eq] at ep
  let u:=((n:ℝ)+1)^p/((N:ℝ)+1)^p
  let w:=(Real.log (r/y)/Real.log 2+1)^p/((N:ℝ)+1)^p
  have uw:u≤w:=div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity:0≤(n:ℝ)+1) (by linarith:(n:ℝ)+1≤Real.log (r/y)/Real.log 2+1) p) (by positivity)
  have pu:0≤u:=by dsimp [u];positivity
  have chain:‖C (radius r n) O‖≤u*‖C (radius r N) O‖ ∧ ‖C (radius r N) O‖≤u*‖C (radius r n) O‖:=by
    dsimp only [u];rw [hk];exact dyadic k O
  change ‖C y O‖≤(2*w)*‖C (radius r N) O‖ ∧ ‖C (radius r N) O‖≤(2*w)*‖C y O‖
  constructor
  · calc
      _≤2*‖C (radius r n) O‖:=ep.1
      _≤2*(u*‖C (radius r N) O‖):=mul_le_mul_of_nonneg_left chain.1 (by norm_num)
      _≤_:=by rw [←mul_assoc];gcongr
  · calc
      _≤u*‖C (radius r n) O‖:=chain.2
      _≤u*(2*‖C y O‖):=mul_le_mul_of_nonneg_left ep.2 pu
      _≤_:=by rw [←mul_assoc,mul_comm u 2];gcongr

include H lead paid raw observed funded hr in
theorem original:Controlled Z F J d r:=fromDyadic Z M H F J lead d raw r hr
  (WilsonPositionScaleLawHomogeneous.original Z F J M H ν lead paid d raw observed funded r hr)

end YM.Integration.WilsonPositionScaleLawContinuum
end
