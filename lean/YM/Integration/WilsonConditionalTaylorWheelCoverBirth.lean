import YM.Integration.WilsonConditionalTaylorWheelFolding
import YM.Integration.WilsonConditionalTaylorWheelTensors

/-! The true signed infinite ultraviolet energy and the independently
constructed normalized cover have identical occupied kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelCoverBirth
open Function Filter Lattice RG Wilson Precision Tree PhysicalNext.Repeat.Legato PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Orb FormalBulk08.Lava FormalBulk08.Shore FormalBulk08.Lotus
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonConditionalTaylorBulkHistory
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem signed {U:Type} [Fintype U] (P:Pal ℝ U) (k:ℕ) (degree:shellK k P) (pure:∀e,Pure (P e)) (e r:ℕ):
    rancho (-flash P) e r= -P e r:=by
  rw [rancho,map_neg]
  change canyon r (-coeff e (flash P))=_
  rw [map_neg]
  exact congrArg Neg.neg (WilsonConditionalTaylorWheelTensors.actual P k degree pure e r)

variable (R:Run G) (simple:G.Simple) (u:G.ColorIndex)
    (wood:∀j,Lodge (R.family.path.levels.clock.op j 0).patch)
    (tags:∀j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include simple in
theorem finite (N:ℕ) (n:Side) (e r:ℕ):
    rancho (course R u wood tags N N n) e (r+1)= -lagoon (moon G e (r+1)) n:=by
  rw [←WilsonConditionalTaylorWheelBirth.original R u wood tags N n,WilsonConditionalTaylorWheelVacuum.signed]
  have H:=Winding.emera_far R.family.path.levels simple R.alloy.B.ratio (le_refl N) n
  rw [signed _ _ H.1 H.2,actionW,story_top]
  change -lagoon (lop (moon G) e (r+1)) n=_
  simp [lop]

include simple tags in
theorem original (N e r:ℕ):
    -actionW R.family.path.levels R.metals.O N N e (r+1)= Dove.model R.family.path.levels
      wood (fun j=>(R.family.path.levels.blocks j 0).branches) R.metals.O u N N e (r+1):=by
  rw [actionW,story_top]
  change -(lop (moon G) e (r+1))=_
  rw [lop,if_neg (Nat.succ_ne_zero _)]
  obtain ⟨_,_,kern⟩:=WilsonConditionalTaylorBulkLimit.full R simple u wood tags N N le_rfl e (r+1) (Nat.succ_pos _)
  obtain ⟨A,expense⟩:=moon_bill G e (r+1) 1 zero_le_one
  have upper:=lagoon_yields expense zero_lt_one (moon_pages G e (r+1)).road
  funext x
  have left:=((upper.point x).neg)
  simp only [dilute,if_neg (Nat.succ_ne_zero _)] at left
  have right:=kern.1 x
  simp only [finite R simple u wood tags N _ e r,Pi.neg_apply] at right
  exact tendsto_nhds_unique left right

end YM.Integration.WilsonConditionalTaylorWheelCoverBirth
end

