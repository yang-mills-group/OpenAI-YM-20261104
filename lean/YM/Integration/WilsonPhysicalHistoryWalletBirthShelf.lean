import YM.Integration.WilsonPhysicalHistoryWalletAxialPacket
import YM.Integration.WilsonConditionalTaylorTailPurchase

/-! The full original source tariff on every radius fitting the actual enrolled
upper representation. Its worst fitting radius is subpower in the true heat
at fixed booked stage, so one lawful numerical threshold buys them all. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletBirthShelf
open Function Filter Finset MeasureTheory Lattice RG RG.Supply Wilson Source Labels Precision Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Roof Push.PriceCompiler
open UVNext.CouplingReset Next.Foundations Graces Roost LocalLTE LocalLTE.Vinca LocalLTE.Concourse
open MergeProof Planned.GuardedAtom Planned.GuardedAtom.Guard Push Push.Local Push.AbsoluteSums
open Extra.Histories RGComparison.Core16.Spool MSbar MSbar.Lis MSbar.Heath MSbar.Midpoint MSbar.Mosaic
open FVA1Physical.Wilson FVA1Physical.Marked FVA1Physical.Round2.Curvature Pressure
open scoped BigOperators Topology Classical
variable {G : Gauge} {I : Type} [Fintype I] {d : ℕ}

theorem monotone (a : I → CoverLabel G d) (H : Stage) : Monotone (fieldShelf a H) := by
  intro r t rt
  have cols : 0≤H.columns := zero_le_one.trans H.columns_ge
  unfold fieldShelf lampFare
  gcongr

theorem below (a : I → CoverLabel G d) (H : Stage) :
    MSbar.Mosaic.Run atTop id (fun x=>fieldShelf a H (radiusB x)) 0 := by
  let n:=Fintype.card I
  have rod : MSbar.Mosaic.Run atTop id (fun x:ℝ=>(radiusB x:ℝ)) 0 :=
    (MSbar.Mosaic.Run.stanza tendsto_id).Yceil tendsto_id (Eventually.of_forall fun x=>sq_nonneg _)
  have one : MSbar.Mosaic.Run atTop id (fun x:ℝ=>1+(radiusB x:ℝ)) 0 :=
    (MSbar.Mosaic.Run.token tendsto_id 1).addR tendsto_id rod
  have bound := (((one.Ypow tendsto_id H.power).mulK tendsto_id ((n+1:ℕ):ℝ)).Ypow tendsto_id H.order).mulY tendsto_id (H.columns^n)
  have fee := (bound.addR tendsto_id (MSbar.Mosaic.Run.token tendsto_id (3*stencilBound (freshLamps a)))).mulK tendsto_id
    (Real.exp (H.supportExponent+2))
  exact fee

theorem all_radii (a : I → CoverLabel G d) (H : Stage) {e : ℝ} (positive : 0<e) :
    ∀ᶠ x : ℝ in atTop, ∀ r≤radiusB x,fieldShelf a H r≤x^e := by
  filter_upwards [below a H e positive] with x fee r hr
  exact ((monotone a H) hr).trans ((le_abs_self _).trans fee)

/-- The original proof's *first* contraction, retained before taking its
coarser inequality. This spends the shelf at the genuine fine heat u+1 and
allows the rest of the physical orbit to use the exact 2/5 rate. -/
theorem first_rate (R : Run G) {N per u : ℕ} (live : u<N) (start : R.t 0≤u) (a : I → CoverLabel G d)
    (b : Site (R.family.side (u+1) per)) (o : I→Site (R.family.side (u+1) per)) (part : Bool) (r : ℕ)
    (placed : ∀ i,separation (o i-b) 0≤r) (fit : r+LocalLTE.Vault.terr G d≤(R.family.path.rep N per (u+1)).p.B) :
    measuredBirth R a N per u b o part r ≤ Doors.rate (R.family.S.block u)*fieldShelf a (R.alloy.B.a.params (u+1)) r := by
  let H:=R.family.path
  let A:=H.rep N per (u+1)
  let h:=R.alloy.B.a.params (u+1)
  let v:=fun i=>o i-b
  let δ:=H.levels.clock.forcedAllowance (u+1)
  have rep:=R.makes.wilson.represents N per (u+1) live
  have advanced : 3 ≤ R.alloy.B.a.clock.J (u+1) := (R.makes.stages 0).1.trans
    (R.alloy.B.a.fits.mono (start.trans (Nat.le_succ _)))
  have slab : A.p=R.alloy.B.a.budget (u+1) := rep.vac
  have permit : hitWidth A.p*Real.sqrt δ ≤ 1 := by
    rw [slab,Blush.glyph_eq]
    exact R.b.stamp _ _ (step_paid R.alloy.B.a (u+1)) 0 ((Nat.zero_le 3).trans advanced) _
      (R.alloy.B.valid.pays (u+1)) |>.2 _ _ (params_eq R.alloy.B.valid (u+1)) rfl
  have bought:=single_ball_fare h A.p a (by rw [slab];rfl) (by rw [slab];rfl) (by rw [slab];rfl)
    r v placed fit part (forcedPos R.alloy.B.a (u+1)) permit
  exact mul_le_mul_of_nonneg_left bought (Doors.rate_pos _).le

theorem aperture (R : Run G) {N per u : ℕ} (live : u<N) :
    (R.family.path.rep N per (u+1)).p.B = radiusB (R.family.path.levels.clock.hatBeta (u+1)) := by
  have slab : (R.family.path.rep N per (u+1)).p = R.alloy.B.a.budget (u+1) :=
    (R.makes.wilson.represents N per (u+1) live).vac
  rw [slab]
  rfl

end YM.Integration.WilsonPhysicalHistoryWalletBirthShelf

