import YM.Integration.WilsonPhysicalStationFactoryGerm

/-! The same registered Wilson input can be read at either of its actual
stations.  These endpoint costs compare the tables with the raw primary
before the thermal or engineering normalizations of the tested coordinates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationRawReading
open Filter Function RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationTableJump (table nominated)
open WilsonPhysicalStationFiledHead (tagged)
open WilsonPhysicalStationFactoryGerm (incoming)
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
  {D:ℕ}(A:Vane R.family D)(d:Fin (D+1))
local notation "F₀" => R.family.labels.level d

def eng (d k:ℕ):ℂ:=(R.family.S.a k:ℂ)^d
def err (k:ℕ):ℝ:=Perch.bill (-1/2) (R.family.path.levels.clock.hatBeta k)

private theorem mass (F:Frame G d)(z:ℂ)(x:F.Coeff):F.coeffSize (z • x)=‖z‖*F.coeffSize x:=by
  simp [Frame.coeffSize,Finset.mul_sum,Pi.smul_apply]

theorem original (y:R.family.label d){N p:ℕ}(check:A.checked f H D)(top:A.k<N):
    (F₀).coeffSize ((incoming R d N p y A.k).x-eng R d A.k • (A.R N p d y)) ≤
      err R A.k*(F₀).coeffSize (incoming R d N p y A.k).x:=by
  let z:=eng R d A.k
  let atGate:=awake R.family d A.k N p y
  have nz:z≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne')
  have recover:z • atGate=(incoming R d N p y A.k).x:=by
    change z • (z⁻¹ • _)=_
    rw [smul_smul,mul_inv_cancel₀ nz,one_smul];rfl
  have price:(F₀).coeffSize (atGate-A.R N p d y)≤err R A.k*(F₀).coeffSize atGate:=(check.rate N p top).2 d y
  change (F₀).coeffSize ((incoming R d N p y A.k).x-z • _ )≤_
  rw [←recover,←smul_sub,mass d,mass d]
  exact (mul_le_mul_of_nonneg_left price (norm_nonneg z)).trans_eq (by ring)

theorem head (w:(Bel R.family.book).Field d){N p:ℕ}(check:A.checked f H D)(top:A.k<N):
    let y:=A.wheel.atCut (N,p) d w
    (F₀).coeffSize ((incoming R d N p y A.k).x-eng R d A.k • tagged R A d w N p)≤
      err R A.k*(F₀).coeffSize (incoming R d N p y A.k).x:=by
  intro y
  rw [←WilsonPhysicalStationFiledHead.exact_calibration R A d w check top]
  exact original R A d y check top

variable {E:ℕ}(V:Vane R.family E)(inside:d.val≤E)
private abbrev card:Fin (E+1):=⟨d.val,Nat.lt_succ_of_le inside⟩

theorem comparison (w z:(Bel R.family.book).Field d){N p:ℕ}(a:A.checked f H D)(ha:A.k<N)
    (b:V.checked f H E)(hb:V.k<N):
    let y:=A.wheel.atCut (N,p) d w
    let want:=eng R d V.k • tagged R V (card d inside) z N p
    let delta:=nominated R A d V inside w z (p:=p) a ha
    (F₀).coeffSize (((incoming R d N p y V.k).x-want)-eng R d V.k • delta)≤
      err R V.k*(F₀).coeffSize (incoming R d N p y V.k).x:=by
  intro y want delta
  have actual:delta=V.R N p (card d inside) y-tagged R V (card d inside) z N p:=by
    change V.R N p (card d inside) ((table R A d (p:=p) a ha).symm (tagged R A d w N p))-_=_ 
    rw [←WilsonPhysicalStationTableJump.stamped R A d w a ha]
  rw [actual,smul_sub]
  change (F₀).coeffSize (((incoming R d N p y V.k).x-want)-(eng R d V.k • V.R N p (card d inside) y-want))≤_
  rw [sub_sub_sub_cancel_right]
  exact original R V (card d inside) y b hb

end YM.Integration.WilsonPhysicalStationRawReading
end
