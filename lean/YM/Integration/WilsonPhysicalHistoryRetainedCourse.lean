import YM.Integration.WilsonPhysicalHistoryRetainedThermal
import YM.Integration.WilsonPhysicalHistoryRetainedWindow

/-! One actual receiving spring and original entered perturbation,
selected before periods, forests, occupied molecules and coarse fields. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem cofinal_integral (R : Run G) (simple : G.Simple) (held : WilsonFundedWindowCompany.PhysicalInputs R.kit)
    (mark : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N n : ℕ, (hq : m+1<N) →
      let A:=R.alloy.B.a
      let k:=A.clock.J (m+1)
      let j:=A.clock.J m
      let P:=R.family.path.rep N n (m+1)
      let Q:=approximation R (p:=n) hq d
      let δ:=(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (m+2))^(d+1)
      let S:=A.clock.op m n
      let T:=Pressure.Testing.ships R.alloy.B N m n
      let D:=R.kit.target k j
      let W:=R.kit.walls k j
      let a:=(R.kit.shape.o k j).a
      ∃ (H : Guide R.alloy.B R.kit.shape N m n P) (b : ℕ→ℝ),
        (∀ v,SumBudget (fun i=>if (P.activities.reg i).site=v then P.p.mass (P.activities.reg i).support (b i) else 0) δ) ∧
        ∀ {F : Forest S.ratio} (X : Coat T F), X.x=A.clock.hatBeta m → X.width=(R.kit.shape.o k j).K → X.manifest →
        ∀ (l : Finset ℕ) (p : Molecule S),
        let err:=fun v : Head S=>(5/2:ℝ)*regularFee S b v
        ∫ t,|X.body P D.table W a l D.halo p t-X.body Q D.table W a l D.halo p t| ∂((F.order G).prod X.dice) ≤
          H.alarms^(blaze p).card*insertedCost (fun v=>H.fair v+err v) err p.toList := by
  have check:= (tendsto_add_atTop_nat 1).eventually (calendar R simple mark checkoutPrice d)
  filter_upwards [check,affine_quarter R simple held,physical_window R simple] with m received house area
  intro N n hq
  dsimp only
  obtain ⟨H,room⟩:=house N n (by omega)
  obtain ⟨b,pay,bill⟩:=molecule_integral R hq (received N n hq)
  refine ⟨H,b,pay,?_⟩
  intro F X clock width mf l p
  exact bill H X clock width mf ((area N n hq).2.2 d)
    (fun y l z i=>room (X.wrapY y) clock width mf l _ z i) l p

end YM.Integration.OriginalMarkedRunAction
