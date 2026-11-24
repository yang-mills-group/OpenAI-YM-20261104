import YM.Integration.FVA1Physical.Sources.Round2.FieldConnected
import YM.Integration.FVA1Physical.Wilson.FluctuationMasks

/-! Weighted mixed and connected readings throughout a thermal-width neighborhood
at every inherited step of the measured trajectory. The measurable incoming density in the
Haar expectation and the native independent Wilson action each have their own
full vacuum. The unit event is proved exactly on both sides. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Set MeasureTheory Marker Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open SectorNext.Vacuum ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool MSbar MSbar.Heath MSbar.Heath.Stock
open MSbar.Midpoint MSbar.Rolling MSbar.Bulk MSbar.Whisk MSbar.Lis MSbar.Cacao MSbar.Bakery MSbar.Bakery.Film
open Tree Pressure Push.Uniform Exterior Comparison.RG02.Order Extra.Trajectories Next.SectorChange
open scoped Classical Topology BigOperators
variable {G:Gauge} {ι:Type} [DecidableEq ι] [Fintype ι] (J:ι→Lamp G)

def ThermalConnectedReadings (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) : Prop :=
  ∀ (C:Census ι) (w:ι→ℝ), (∀i,0<w i) → ∀ p s L:ℕ, 6 ≤ s → ∀ D η:ℝ, 0 ≤ D → 0 < η →
    ∀ᶠ k:ℕ in atTop,∀ N n, k ≤ N →
      (∃ S:Scene R.family.path.levels n (p+2), Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S) ∧
      ∀ (S:Scene R.family.path.levels n (p+2)) (scene:Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S),
        ∀ (j:ℕ) (kj:k ≤ j) (jN:j < N),
          let F:=(scene.step j jN kj).choose;let v:=(scene.step j jN kj).choose_spec.choose
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let y:=R.family.path.levels.clock.hatBeta (j+1)
          S.Poly j=A.Zpost R.metals.O ∧
            ∀ (b:Site A.f) (Z:Positions (Primary A.c G)), ‖A.fClock • Z‖ ≤ D*Heath.Cottage.room y → ∀ o:ι→Site A.f,
            (∀ l:Slice J,separation b (legs J o l).1 ≤ L*Mosaic.closeN y) →
            let P:=fullFieldTable J C A Z o;let Q:=wilsonFieldTable J C A R.metals.O p Z o
            let E:=A.fClock^((p:ℝ)+1-η)
            P.part C.quiet=1 ∧ Q.part C.quiet=1 ∧ Poly.price w (P-Q)≤E ∧
              Poly.price w (connected P-connected Q)≤E

theorem connected_from_thermal (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex)
    (all:FluctuationMaskReadings J R u) : ThermalConnectedReadings J R u := by
  intro C w hw p s L hs D η hD hη
  let δ:=min (η/2) (1/2)
  have hδ:0<δ:=lt_min (half_pos hη) (by norm_num)
  have dh:δ<η:=(min_le_left ..).trans_lt (half_lt_self hη)
  have dp:δ≤1/2:=min_le_right .. 
  let K:=markerScale C w (2*maskEnvelope J)
  have K0:0≤K:=markerScale_nonneg C w hw (mul_nonneg zero_le_two (maskEnvelope_pos J).le)
  have K1:0<1+K:=by linarith only [K0]
  filter_upwards [all p s L hs D δ hD hδ,
    actual_clock_small R.family.path (q:=η-δ) (d:=(1+K)⁻¹) (sub_pos.mpr dh) (inv_pos.mpr K1) hG R.T.choice,
    actual_clock_small R.family.path (q:=1) zero_lt_one zero_lt_one hG R.T.choice] with k masks small unit
  intro N n kN
  obtain ⟨existsS,book⟩:=masks N n kN
  refine ⟨existsS,?_⟩
  intro S scene j kj jN F v A y
  obtain ⟨poly,cash⟩:=book S scene j kj jN
  refine ⟨poly,?_⟩
  intro b Z hZ o near P Q E
  let g:=A.fClock
  have hg:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson jN))
  have je:=kj.trans (Nat.le_succ j)
  have h1:=unit (j+1) je N n jN
  change g^(1:ℝ)≤1 at h1
  rw [Real.rpow_one] at h1
  have sn:=small (j+1) je N n jN
  change g^(η-δ)≤(1+K)⁻¹ at sn
  have scale:K*g^(η-δ)≤1:=by
    apply (mul_le_mul (le_add_of_nonneg_left zero_le_one) sn (Real.rpow_nonneg hg.le _) K1.le).trans_eq
    exact mul_inv_cancel₀ K1.ne'
  have rate:K*g^((p:ℝ)+1-δ)≤E:=by
    rw [show (p:ℝ)+1-δ=((p:ℝ)+1-η)+(η-δ) by ring, Real.rpow_add hg]
    calc _=g^((p:ℝ)+1-η)*(K*g^(η-δ)):=by ring
         _≤_:=mul_le_of_le_one_right (Real.rpow_nonneg hg.le _) scale
  have one: g^((p:ℝ)+1-δ)≤1 := Real.rpow_le_one hg.le h1 (by linarith only [dp,Nat.cast_nonneg (α:=ℝ) p])
  let chain:=RunFormalChain.fromRun R
  have tr:=(scene.budget (j+1) jN je).1
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [chain.clips N n (j+1) jN,chain.selected N n (j+1) jN]
    exact blueprint F v (chain.kin.path N (j+1)) _ (R.family.path.levels.blocks j n).branches tr.quiet
      (chain.post.price _) (chain.planned.gap N j n jN F)
  let st:=R.family.path.levels.params (j+1)
  let clock:=R.family.path.levels.clock
  let O:=postcard G A.c A.fClock Z
  have mass:=(strictly R.family.path R.T.choice N n j jN.le O).trans_eq (congrFun (R.T.choice.steps N n j jN).1 O)
  have adm:Admitted O A.pre A.S st.width st.paths (clock.allowance (j+1)) (clock.loopCap (j+1)) (clock.forcedAllowance (j+1)) :=
    ⟨(R.T.choice.represents N n (j+1) jN).good,fun X=>(strictly R.family.path R.T.choice N n (j+1) jN X).le,
      mass,R.family.path.levels.transition_mass j n A.pre.beta⟩
  obtain ⟨qP,qQ,raw,logarithm⟩:=field_mask_prices J C A R.metals.O p L y δ b Z o w hw near adm tr.bond pd (cash b Z hZ) one
  exact ⟨qP,qQ,raw.trans rate,logarithm.trans rate⟩

/-- A single construction, chosen before the marker census, weights, order, tests,
and all admissible periods, pays the complete finite connected physical sector. -/
theorem thermal_connected_trajectory {goal:Goal G} (extra:Obtainable goal) (hG:G.Simple) (penalty:ℝ) (hp:0<penalty) :
    ∃ (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) (V:Voice G),
      R.family.path.levels.clock.kernel.penalty=penalty ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ Clear G V ∧ Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧
      ThermalConnectedReadings J R u := by
  obtain ⟨R,u,V,pen,other,frame,cle,docket,masks⟩:=fluctuation_mask_trajectory J extra hG penalty hp
  exact ⟨R,u,V,pen,other,frame,cle,docket,connected_from_thermal J hG R u masks⟩
end YM.Integration.FVA1Physical.Round2.Curvature
