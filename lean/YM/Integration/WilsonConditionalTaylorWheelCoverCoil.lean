import YM.Integration.WilsonConditionalTaylorWheelFiniteCoil
import YM.Integration.WilsonConditionalTaylorWheelCoilLimit

/-! Equality by uniqueness of *one* physical period limit at each
cutoff and date. No common convergence rate for the independent Kith
at different cutoffs is used. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelCoverCoil
open Function Filter Lattice Laurent RG Wilson Exterior Precision Tree Bloch Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos PhysicalNext.Repeat.Legato
open Next.Free FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof Lotus Mesa
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) (u:G.ColorIndex) (N j:ℕ)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
local notation "W" => Dove.model V wood b R.metals.O u N (j+1)
local notation "P" => destination V N j
local notation "raw" => FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j)

include simple in
theorem identity (live:j<N) (E e r c q degree:ℕ) (width:Gear G→ℝ)
    (positive:∀I,0<width I) (Q:Realm G (E+1) Credit.leanC) (here:Q.anchor≤j)
    (invoice:RootedVacuumWinding.ReceiptOn R E e r c q degree width j Q here)
    (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (same:∀per:ℕ,let n:=R.family.side j per;
       (-(coil0 V R.metals.O j N n e (r+1)))=rancho (FormalBulk08.Bank.burn P (wood j) W R.metals.O (b j) tags n) e (r+1)):
    -freshet V R.metals.O N j e (r+1)=raw e (r+1):=by
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  obtain ⟨η,_,step⟩:=FormalBulk08.Bank.componentwise P (wood j) W R.metals.O (b j) dossier
    ((V).clock.adm j) R.alloy.B.ratio tags e (r+1) (0:Fin (r+1))
  funext x
  have actual:=(WilsonConditionalTaylorWheelCoilLimit.original R simple positive Q here invoice N live x).neg
  have priced:=(step.1 x).comp (WilsonUniformUnmarkedSpatialLimit.sides R j)
  apply tendsto_nhds_unique actual
  refine priced.congr' (Eventually.of_forall (fun per=>?_))
  exact (congrFun (same per) (foldUnder (R.family.side j per) ∘ x)).symm

include simple in
theorem positive (live:j<N) (E e r c q degree:ℕ) (width:Gear G→ℝ)
    (positiveWidth:∀I,0<width I) (Q:Realm G (E+1) Credit.leanC) (here:Q.anchor≤j)
    (invoice:RootedVacuumWinding.ReceiptOn R E e r c q degree width j Q here)
    (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (previous:∀d≤E,∀s<d+2,-actionW V R.metals.O N (j+1) d (s+1)=W d (s+1))
    (pos:0<e) (cap:e≤E):
    -freshet V R.metals.O N j e (r+1)=raw e (r+1):=
  identity R simple u N j live E e r c q degree width positiveWidth Q here invoice tags
    (fun per=>WilsonConditionalTaylorWheelFiniteCoil.original R simple u N j tags live E previous per e r pos cap)

end YM.Integration.WilsonConditionalTaylorWheelCoverCoil
end
