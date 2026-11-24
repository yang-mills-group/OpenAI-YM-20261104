import YM.Integration.WilsonConditionalTaylorWheelPhysicalSide
import YM.Integration.WilsonVacuumPreResetIndependentBirth
import YM.Integration.WilsonVacuumPreResetFoldedCopyMoments
import YM.Integration.WilsonConditionalTaylorWheelClassicalHead
import YM.FormalBulk08.Bank.Tee

/-! The finite folded update is compared to the independently filed position prescription at fixed top.
The full classical kinetic row agrees before and after this limit on every interior date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetIndependentCoil
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) (u:G.ColorIndex) (N j:ℕ)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
local notation "W" => Dove.model V wood b R.metals.O u N (j+1)
local notation "P" => destination V N j


theorem sides {G:Gauge}(R:Run G)(j:ℕ):Tendsto (R.family.side j) atTop atTop:=by
  have grow:StrictMono (fun t:ℕ=>(R.family.side j t).val):=
    fun _ _ h=>Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator j).pos
  exact tendsto_atTop.2 fun n=>grow.tendsto_atTop.eventually_ge_atTop n.val

theorem signed {U:Type}[Fintype U](T:Pal ℝ U)(k:ℕ)(shape:shellK k T)(pure:∀e,Pure (T e))(e r:ℕ):
    rancho (-Blue.flash T) e r= -T e r:=by
  rw [rancho,map_neg]
  change Lava.canyon r (-(PowerSeries.coeff e (Blue.flash T)))=_
  rw [map_neg]
  exact congrArg Neg.neg (WilsonVacuumPreResetIndependentBirth.actual T k shape pure e r)

include simple in
theorem from_finite (live:j<N)(e r:ℕ)
    (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (same:∀per:ℕ,let n:=R.family.side j per;
      -(coil0 V R.metals.O j N n e (r+1))=rancho (FormalBulk08.Bank.burn P (wood j) W R.metals.O (b j) tags n) e (r+1)):
    -freshet V R.metals.O N j e (r+1)=FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j) e (r+1):=by
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  obtain ⟨_,_,step⟩:=FormalBulk08.Bank.componentwise P (wood j) W R.metals.O (b j) dossier
    ((V).clock.adm j) R.alloy.B.ratio tags e (r+1) (0:Fin (r+1))
  funext x
  have actual:=(((WilsonVacuumPreResetFoldedCopyMoments.output R simple live e (r+1)).point x).comp (sides R j)).neg
  simp only [dilute,if_neg (Nat.succ_ne_zero _)] at actual
  have formal:=(step.1 x).comp (sides R j)
  apply tendsto_nhds_unique actual
  refine formal.congr' (Eventually.of_forall (fun per=>?_))
  exact (congrFun (same per) (foldUnder (R.family.side j per) ∘ x)).symm

include simple in
theorem finite (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (live:j<N) (per r:ℕ):
    let n:=R.family.side j per;
    (-(coil0 V R.metals.O j N n 0 (r+1)))=
      rancho (FormalBulk08.Bank.burn P (wood j) W R.metals.O (b j) tags n) 0 (r+1):=by
  intro n
  let S:=(V).clock.op j per
  let f:=R.family.side (j+1) per
  let X:=Winding.emera (actionW V R.metals.O N (j+1)) f
  let F:=repeatF S
  let H:=freeForms V N (j+1)
  let Y:=freeForms V N j
  let M:=installed S.ratio (predictionA V N j)
  let T:=winter S F H Y M R.metals.O X
  have present:coil0 V R.metals.O j N n=T:=WilsonConditionalTaylorWheelPhysicalSide.original R N j per
  have available:=Winding.emera_far V simple R.alloy.B.ratio (Nat.succ_le_iff.mpr live) f
  have shape:shellK 2 T:=winter_band S F H Y M R.alloy.B.ratio available.1
  have purity:∀a,Pure (T a):=winter_pure S F H Y M R.alloy.B.ratio ((V).blocks j per).branches
    available.2 (age_sym V ..)
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  have file:=FormalBulk08.Bank.funded P (wood j) W R.metals.O (b j) dossier
    ((V).clock.adm j) R.alloy.B.ratio tags n
  have real:=WilsonConditionalTaylorWheelClassicalHead.recorded R N j per F X
  dsimp only at real
  rw [loc_land V N j live] at real
  rw [present,←signed T 2 shape purity 0 (r+1)]
  exact congrArg (Lava.marble (r+1)) (real.trans file.symm)


include simple in
theorem classical (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (live:j<N)(r:ℕ):
    -freshet V R.metals.O N j 0 (r+1)=FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j) 0 (r+1):=
  from_finite R simple u N j live 0 r tags (fun per=>finite R simple u N j tags live per r)

end YM.Integration.WilsonVacuumPreResetIndependentCoil
