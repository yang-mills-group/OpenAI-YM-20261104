import YM.Integration.WilsonPositionScaleLawGuardFlat

/-! Lower grades are flat to every inverse logarithmic power at every original radius in a fixed ultraviolet interval. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardAnnulus
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawGuardOrbit (size sizePos total)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGuardPhysical (expected)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawWholeGrowth (weight)
open scoped Topology Classical Asymptotics

theorem age (r:ℝ)(hr:0<r)(n:ℕ)(t:Ratio):
    1+Real.log (r/(t.val*radius r n))/Real.log 2≤((n:ℝ)+1)+1:=by
  have rn:0<radius r n:=by change 0<r*(1/2:ℝ)^n;positivity
  have next:0<radius r (n+1):=by change 0<r*(1/2:ℝ)^(n+1);positivity
  have lo:radius r (n+1)≤t.val*radius r n:=by
    rw [←WilsonPositionScaleLawWholeGrowth.next]
    exact mul_le_mul_of_nonneg_right t.property.1 rn.le
  have pos:=mul_pos (WilsonPositionScaleLawNative.positive t) rn
  have date:=WilsonPositionScaleLawClock.logRadius r hr (n+1)
  change Real.log ((radius r (n+1))⁻¹)=(↑(n+1):ℝ)*Real.log 2-Real.log r at date
  rw [Real.log_inv,Nat.cast_add_one] at date
  have fee:=Real.log_le_log next lo
  have upper:Real.log (r/(t.val*radius r n))/Real.log 2≤(n:ℝ)+1:=by
    apply (div_le_iff₀ (Real.log_pos (by norm_num:1<(2:ℝ)))).mpr
    rw [Real.log_div hr.ne' pos.ne']
    linarith
  linarith

variable {G:Gauge}
variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
variable (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:∀q,WilsonPositionScaleLawGuardLittle.scale F J Z M ν d q)(r:ℝ)(hr:0<r)
open WilsonPositionScaleLawGrade (grade half)
open WilsonPositionScaleLawGuardForcing (amount)
def Controlled (i:Fin (d+1))(m:ℕ):Prop:=∃ρ:ℝ,0<ρ ∧ ∀O:S.Field d,∃B:ℝ,0≤B ∧ ∀u:ℝ,0<u→u≤ρ→
    (1+Real.log (r/u)/Real.log 2)^m*‖grade R.family i (physical F J Z d u O)‖≤B

include H funded law hr in
theorem original (i:Fin (d+1))(lower:i.val<d)(m:ℕ):Controlled Z F J d r i m:=by
  obtain ⟨K,heads⟩:=WilsonPositionScaleLawGuardFlat.dyadic Z M H ν F J d funded law r hr i lower m
  obtain ⟨q,N,fees⟩:=WilsonPositionScaleLawGuardForcing.original Z M H ν F J d funded law r hr m
  have raw:=(WilsonPositionScaleLawClock.falls r hr).eventually (WilsonPositionScaleLawGuardBlock.original Z M H ν F J funded q i lower)
  obtain ⟨L,steps⟩:=eventually_atTop.mp raw
  let D:=max K (max N L)
  have hK:K≤D:=le_max_left ..
  have hN:N≤D:=(le_max_left N L).trans (le_max_right ..)
  have hL:L≤D:=(le_max_right N L).trans (le_max_right ..)
  refine ⟨radius r D,show 0<r*(1/2:ℝ)^D by positivity,?_⟩
  intro O;obtain ⟨A,hA,priced⟩:=heads O;obtain ⟨B,hB,sold⟩:=fees O
  let P:=grade R.family i
  let a:=4*2^m*A
  let b0:=4*‖P‖*B
  have ha:0≤a:=by dsimp [a];positivity
  have hb:0≤b0:=by dsimp [b0];positivity
  refine ⟨a+b0,add_nonneg ha hb,?_⟩;intro u hu tiny
  obtain ⟨n,hn,t,link,days⟩:=WilsonPositionScaleLawContinuum.band r hr D u hu tiny
  let y:=physical F J Z d u O
  let x:=physical F J Z d (radius r n) O
  let cost:=amount Z M ν F J d r q n t
  let w:=weight m (n+1)
  have hw:0≤w:=zero_le_one.trans (WilsonPositionScaleLawWholeGrowth.positive ..)
  have next:=steps n (hL.trans hn) t O
  dsimp only at next
  rw [link] at next
  change 3*‖P y‖≤4*t.val*‖P x‖+4*‖P‖*cost*‖y‖ at next
  have source:=sold n (hN.trans hn) t
  rw [link] at source
  have edge:w*cost*‖y‖≤B:=source
  have base:w*‖P x‖≤2^m*A:=calc
    _≤(2^m*weight m n)*‖P x‖:=mul_le_mul_of_nonneg_right (WilsonPositionScaleLawGuardForcing.shift m n) (norm_nonneg _)
    _=2^m*(weight m n*‖P x‖):=mul_assoc .. 
    _≤_:=mul_le_mul_of_nonneg_left (priced n (hK.trans hn)) (by positivity)
  have ht:4*t.val*‖P x‖≤4*‖P x‖:=by
    exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left t.property.2 (by norm_num : (0:ℝ)≤4)).trans_eq (mul_one _)) (norm_nonneg _)
  have weighted:=mul_le_mul_of_nonneg_left (next.trans (add_le_add ht le_rfl)) hw
  have spill:=mul_le_mul_of_nonneg_left edge (mul_nonneg (by norm_num : (0:ℝ)≤4) (norm_nonneg P))
  have row:w*‖P y‖≤a+b0:=by
    dsimp only [a,b0]
    linarith only [weighted,spill,base,mul_nonneg hw (norm_nonneg (P y))]
  have late:=age r hr n t
  rw [link] at late
  have fee:(1+Real.log (r/u)/Real.log 2)^m≤w:=by
    change (1+Real.log (r/u)/Real.log 2)^m≤((↑(n+1):ℝ)+1)^m
    rw [Nat.cast_add_one]
    exact pow_le_pow_left₀ (by linarith only [days,Nat.cast_nonneg (α:=ℝ) n]) late m
  exact (mul_le_mul_of_nonneg_right fee (norm_nonneg (P y))).trans row

end YM.Integration.WilsonPositionScaleLawGuardAnnulus
