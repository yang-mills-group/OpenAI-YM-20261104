import YM.Integration.WilsonOriginalTwoFlatTap
import YM.Integration.WilsonOriginalOccupiedReturn
import YM.Integration.WilsonOriginalJointTrialHearing

/-! Amplify at the true birth, carry each tap to the common housing, and
read at any older original flat without spending its wallet on that gap. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatWithdrawal
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedTap WilsonOriginalOccupiedSource WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor
open WilsonThermometerUnitFilingCoarse (reading)
open private tower from YM.Integration.WilsonOriginalJointTrialHearing
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b t:ℕ}
variable {V:Type} [DecidableEq V] [Fintype V] {marks:Marker.Census V}
variable (way:WayStation R.kit) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (ticket:TicketP R.alloy R.kit D Q)
  {X I:Type} [Countable I] [Nonempty X] (o:V → Site (R.family.side t per))
  (A:Gallery X I o (Ψ t) marks)(w:V → ℝ)(wp:∀v,0<w v)

variable (simple:G.Simple){u i:ℕ}(floor:m ≤ u)(ub:u ≤ b)
    (fixed:WilsonSingleHardRadius.first R simple ≤ u)(capture:WilsonCenteredCaptureClock.first R simple ≤ b)
    (ui:u ≤ i)(ib:i ≤ b)(bt:b<t)(top:t ≤ N)
    (Z₀:Support (R.family.side b per))(center:Site (R.family.side b per))(home:center∈Z₀)
local notation "κc" => LocalComparison.forcedDivisor R.family b
local notation "βc" => R.alloy.B.a.clock.hatBeta b

include course ticket way wp simple floor ub fixed capture ui ib bt top home in
theorem taps {load:ℕ}
    (stage:∀k,b ≤ k → load ≤ R.alloy.B.a.clock.J k)(load_ok:∀s:marks.Mode,s.val.card ≤ load)
    (cap:∀k,b ≤ k → LocalComparison.forcedDivisor R.family k ≤ 1)
    (s:marks.Mode)(anchors:∀v∈s.val,sites R o bt.le v∈Z₀)
    (n:ℕ)(size:s.val.card ≤ n)(T q:ℂ)(inv:T*q=1)(small:‖q‖ ≤ 1)
    (regular:A.E.Paid w (Ψ t).p.B (Ψ t).p.supportExponent 1)
    (paid:∀z∈nodes n T,(gallery z A).K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent 1)(x:X):
    let money:=Poly.toll (wallet R w bt.le) s
    let roof:=((shards marks s).card:ℝ)+4*(money+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z₀ 1 s.val.card)*βc*κc
    money*‖(((Ψ i).eval 1:ℂ)⁻¹)*((gust R.family.path N per t (A.density x) i (ib.trans bt.le) 1).part s-
        (gust R.family.path N per t ((gallery 0 A).density x) i (ib.trans bt.le) 1).part s)‖ ≤
      (‖q‖*price n)*roof:=by
  intro fee roof
  let Z:=(fun z:ℂ=> (gallery z A).density x)
  let Y:=(fun z:ℂ=>(gust R.family.path N per t (Z z) i (ib.trans bt.le) 1).part s)
  let vac:=((Ψ i).eval 1:ℂ)⁻¹
  let J:=fun i:Fin (n+1)=>T*node i
  have live (i:Fin (n+1)):J i∈nodes n T:=
    mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))
  have pack (z:ℂ)(hz:z∈nodes n T):(gallery z A).Pays w (Ψ t).p.supportExponent 1 1:=⟨regular,paid z hz⟩
  have law:=(course.1.walk t ((floor.trans ub).trans bt.le) top).truep.valid
  have income (z:ℂ)(hz:z∈nodes n T):Integrable (Z z) (prior G _):=
    QuadraticLocal.Tariff.integrable marks o w wp (gallery z A) x (pack z hz) (Ψ t).p.exponent_pos.le law
  have stencil:=WilsonOriginalOccupiedTransport.original R (N:=N) (Z 1) (Z 0) (fun j=>Z (J j)) (weight q) s (ib.trans bt.le)
    (income 1 (by simp [nodes])) (income 0 (by simp [nodes])) (fun i=>income _ (live i))
    (WilsonOriginalOccupiedSource.original A w wp s size T q inv paid x) 1
  have physical : Z 1=A.density x:=funext (WilsonOriginalOccupiedSource.one A x)
  change Y 1 - Y 0 = ∑i:Fin (n+1),weight q i*Y (J i) at stencil
  have active : 0 < fee:=Poly.worth (positive R w wp bt.le) s
  have quiet:(Ψ i).eval=(R.family.path.rep N per i).eval:=(course.1.walk i (floor.trans ui) ((ib.trans bt.le).trans top)).view
  have costs (a:Fin (n+1)):fee*‖vac*Y (J a)‖ ≤ roof:=by
    obtain ⟨ι,L,count,base,opened,output⟩:=WilsonOriginalOccupiedCorridor.original R way D Q π Γ Ψ course ticket
      o (gallery (J a) A) w wp (floor.trans ub) top bt.le stage load_ok cap (pack _ (live a))
    letI:Countable ι:=count
    have incomes:=opened bt
    have wp':=positive R w wp bt.le
    have strong:=WilsonOriginalTwoFlatTap.original R π Γ Ψ course (bt.trans_le top)
      (R.family.localSection 0) R.family.params simple way D Q ticket floor ub fixed capture
      (cap b le_rfl) (sites R o bt.le) L x s Z₀ center home anchors (wallet R w bt.le) wp'
      base.1 incomes.1 incomes.2 ui ib
    have integrable:=QuadraticLocal.Tariff.integrable marks (sites R o bt.le) (wallet R w bt.le) wp' L x base
      (Ψ b).p.exponent_pos.le (course.1.walk b (floor.trans ub) (bt.le.trans top)).truep.valid
    have seen:reading R (N:=N) (fun U=>(L.density x U).part s) i ib=vac*Y (J a):=by
      unfold reading
      rw [←WilsonOriginalOccupiedTransport.projected R (L.density x) integrable s ib]
      change _*(gust R.family.path N per b (L.density x) i ib 1).part s=_
      have up:L.density x=gust R.family.path N per t (Z (J a)) b bt.le:=output x
      rw [up,←tower R N per (Z (J a)) ib bt.le]
      dsimp only [vac,Y];rw [quiet]
    simpa only [seen] using strong
  have exact_read:vac*(Y 1-Y 0)=∑i:Fin (n+1),weight q i*(vac*Y (J i)):=by
    rw [stencil,mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [←physical]
  change fee*‖vac*(Y 1-Y 0)‖ ≤ _
  rw [exact_read]
  calc
    _ ≤ fee*∑i:Fin (n+1),‖weight q i*(vac*Y (J i))‖:=mul_le_mul_of_nonneg_left (norm_sum_le ..) active.le
    _ = ∑i:Fin (n+1),‖weight q i‖*(fee*‖vac*Y (J i)‖):=by
      rw [mul_sum];apply sum_congr rfl;intro i _;rw [norm_mul];ring
    _ ≤ ∑i:Fin (n+1),‖weight q i‖*roof:=
      sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (costs i) (norm_nonneg _)
    _ ≤ _:=by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (earned n q small) ((mul_nonneg active.le (norm_nonneg _)).trans (costs 0))

include course ticket way wp simple floor ub fixed capture ui ib bt top home in
theorem original {load:ℕ}
    (stage:∀k,b ≤ k → load ≤ R.alloy.B.a.clock.J k)(load_ok:∀s:marks.Mode,s.val.card ≤ load)
    (cap:∀k,b ≤ k → LocalComparison.forcedDivisor R.family k ≤ 1)
    (s:marks.Mode)(anchors:∀v∈s.val,sites R o bt.le v∈Z₀)
    (n:ℕ)(np:0<n)(size:s.val.card ≤ n)
    (tiny:WilsonOriginalOccupiedWallet.inverseAmplitude n (LocalComparison.forcedDivisor R.family t) ≤ 1)
    (regular:A.E.Paid w (Ψ t).p.B (Ψ t).p.supportExponent 1)
    (hard:A.K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent (LocalComparison.forcedDivisor R.family t))(x:X):
    let money:=Poly.toll (wallet R w bt.le) s
    let roof:=((shards marks s).card:ℝ)+4*(money+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z₀ 1 s.val.card)*βc*κc
    money*‖(((Ψ i).eval 1:ℂ)⁻¹)*((gust R.family.path N per t (A.density x) i (ib.trans bt.le) 1).part s-
      (gust R.family.path N per t (fun U=>((Ψ t).eval U:ℂ) • Poly.pass (A.E.log x U)) i (ib.trans bt.le) 1).part s)‖ ≤
      (WilsonOriginalOccupiedWallet.inverseAmplitude n (LocalComparison.forcedDivisor R.family t)*price n)*roof:=by
  intro money roof
  let κ:=LocalComparison.forcedDivisor R.family t
  let q:=WilsonOriginalOccupiedWallet.inverseAmplitude n κ
  have kp:0<κ:=Real.sqrt_pos.2 (Real.exp_pos _)
  have qp:0<q:=by dsimp [q,WilsonOriginalOccupiedWallet.inverseAmplitude];positivity
  have fund:=WilsonOriginalOccupiedWallet.enrolled A w wp n np κ kp tiny hard
  have inv:((q⁻¹:ℝ):ℂ)*(q:ℂ)=1:=by exact_mod_cast inv_mul_cancel₀ qp.ne'
  have small:‖(q:ℂ)‖=q:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos qp]
  have h:=taps R way D Q π Γ Ψ course ticket o A w wp simple floor ub fixed capture ui ib bt top Z₀ center home
    stage load_ok cap s anchors n size (q⁻¹:ℝ) (q:ℂ) inv (small.le.trans tiny) regular fund x
  have erase:=funext fun U=>WilsonOriginalOccupiedWallet.origin A x U w wp (fund 0 (by simp [nodes]))
  rw [erase,small] at h
  exact h

end YM.Integration.WilsonOriginalTwoFlatWithdrawal
end
