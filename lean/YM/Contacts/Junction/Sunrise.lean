import YM.Contacts.Junction.Turbine
/-! # per-station Rate-frame supplies for wire Hull. All Stage clocks initially fixed.
 Auxiliary side can vary. Includes moving-tree chart hands. Path stencils actually assembled
 (E payments separately). At this point just support conditional. 
 -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} (P : ChartRatio G) {σ C e a v d t K:ℝ}{n k j i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current
open Sienna Lantern
-- Fuel for one fixed payment-frame step. Need station chart pre availability order j+3 in Service; circular P? see notes.Work.S.W. `hut` amplitude pm.O. Assembly tasks.
structure Dew (G:Gauge) where
    c : Side
    f : Side
    S : StepData c f
    T : Tube G S
    B : Forest S.ratio
    ρ : (Bid.Dir G c)→ AxisChart G B
    β : ℝ
namespace Dew
variable (t:Dew G)
abbrev X:= Anchor G t.c
abbrev Y:= Truck G t.B
abbrev Q:= (ℝ× t.X) × t.Y
abbrev L : t.X→L[ℝ] t.Y:= seam t.B t.ρ
abbrev grad : ℝ:= Coat.gStep t.β
abbrev label:= art t.S
abbrev matrix := Lapis.gram t.B t.T.up t.T.high t.ρ t.label 0
abbrev ℓ (t:Dew G): t.Q→L[ℝ] (t.X× t.Y):= localL t.B (t.L)
abbrev ℘ : t.X →ℝ:= camber (Lapis.table t.B t.label t.T.up t.T.high) t.L
abbrev fan := ribbon P t.B t.T t.label t.L
-- numbers.Unscaled model Bnd income Theta.Manifest.Quilt post. Defender sends using EXIST.B
structure Pearl (κ:Teller G) (v x:ℝ) (L:Side)(σ C:ℝ)(M:Uniform.ChartPrices)(n:ℕ)(b:BudgetPoint)(t:Dew G):Prop where
    service : ∃ U : Before G σ C t.S.patch.J t.S.kernel (n+3), U.Service t.B t.T.high t.T.up t.ρ∧ U.tables t.T.high t.S.patch=M
    patch : t.S.patch.L=L
    stitches : Quilt t.T t.B v
    staples : t.T.up.Bounds t.T.high σ C (loopBill G L x)
    intake : Intake κ t.T x (Pane.virgin t.T b t.β)
    palette : t.B = YM.Pulse.Spine.Larch.planting t.S.ratio t.S.patch.odd_side -- irrelevant to rates first
end Dew
open Dew
variable {U:Teller G}{D:ℕ→Dew G}{g v f K a w:ℕ→ℝ}{b:ℕ→BudgetPoint}{L:Side} {M:Uniform.ChartPrices}
variable {N:Meter} (hp:Pouch N (- (1/2:ℝ)) g)
local notation "Φ" => (fun i=> Dew.Q (D i))
local notation "E" => Frame.Port Φ (N.pow Capture.stashp)
variable (ht: ∀ᶠ i in atTop,Pearl U (v i) (f i) L σ C M n (b i) (D i)) (hv:N.Rush 0 v) (he: N.β=ᶠ[atTop] (fun i=> betaF G (f i) L)) (hh:Tendsto f atTop atTop)
local notation "J" => (fun i=> Dew.L (D i))
include ht hv
lemma wordPos : 0<M.gap∧0<M.horizon∧0<M.value∧0<M.initial ∧0<M.safety:= by
    obtain ⟨i,hp⟩:= ht.exists; obtain ⟨P,hy,rfl⟩:= hp.service; let t:=D i; let M:=P.tables t.T.high t.S.patch; have hx := P.receipt t.B t.label hp.staples hp.stitches.large rfl rfl|>.1; exact ⟨hx.pos_m,hy.x_pos, hx.pos_C,hx.pos_r,hy.x_pos.trans_le (hy.2.1.trans hy.2.2.2.1)⟩ -- edit last
open Uniform
lemma chairCost (P:ChartPrices)(h:N.Rush 0 v) : let q i:= v i*lensT n P (v i); N.Rush 0 q∧ N.Rush 0 (fun i=>mineshaft n P (v i)) := by
   have hh k (y:ℝ): N.Rush 0 (fun i=> tollS (v i) k y):= (Rush.zeroN _ h).bind _; unfold mineshaft; exact ⟨h.times ((Rush.settle _).blend (hh _ _)) (by norm_num), (hh _ _).bind _⟩ -- hh.Scope.H arg
lemma seamBill : N.Rush 0 fun i=>‖(D i).L‖:= by
    let f i:= v i*lensT n M (v i); apply Rush.bb (chairCost (N:=N) ht hv M hv|>.1); filter_upwards [ht] with i hi; obtain ⟨A,hA,hM⟩:= hi.service; let d i:=‖(D i).L‖; refine ⟨norm_nonneg _, ?_⟩; let D:=D i; have h:= luminous D.B D.label D.T.up D.T.high D.ρ σ C _ A hi.stitches.large hi.staples hA _ hi.stitches.one hi.stitches.overall _ (mem_ball_self hA.x_pos); rw [← hM]; exact (norm_iteratedFDeriv_one (𝕜:=ℝ) _).symm.trans_le ((Brush.offer.1 h).2 1 (by omega))
variable {V:ℕ→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] -- E notation error remove
lemma slope (t:Dew G): ‖t.ℓ‖ ≤ (1+‖t.L‖):= by
   apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg zero_le_one (norm_nonneg _)); intro z; let x:= z.1.2; let v:= z.2; have hx : ‖x‖≤ ‖z‖:= (norm_snd_le _).trans (norm_fst_le _); have hv: ‖v‖≤ ‖z‖:= norm_snd_le _; change ‖(x,t.L x+v)‖≤ _; rw [Prod.norm_def,add_mul,one_mul]; refine max_le (hx.trans (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)))) ?_; rw [add_comm ‖z‖]; exact (norm_add_le ..).trans (add_le_add ((t.L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))) hv)
lemma ℓ_price: N.Rush 0 (fun i=>‖(D i).ℓ‖):= Rush.bb ((Rush.settle 1).blend (seamBill ht hv)) (Eventually.of_forall fun i=> ⟨norm_nonneg _, slope (ht:=ht) (hv:=hv) (D i)⟩) -- omit ht
lemma ell_pole : Direct N k 0 (N.pow Capture.stashp) (fun i=>⇑(D i).ℓ) := Arms.project _ (N:=N) (Current.meetP Meter.Rush.any (by norm_num [Capture.stashp])) (ℓ_price ht hv) (add_zero _)
lemma K_use {d:ℝ} (h:stashp <d) : ∀ᶠ i in atTop,∀ z∈Frame.Bank Φ (N.pow stashp) i, ‖(D i).ℓ z‖ < N.pow d i:= by
   have hr:= ℓ_price ht hv; have hs:= rush_lax (hr.times Meter.Rush.any (zero_add stashp)) h; refine hs.mono fun i hi x hx=>?_ ; apply lt_of_le_of_lt (((D i).ℓ.le_opNorm x).trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le (norm_nonneg _))) ((le_abs_self _).trans_lt hi)
lemma K_touch {r:ℝ} (hr:0<r) : ∀ᶠ i in atTop,∀ z∈ Frame.Bank Φ (N.pow Capture.stashp) i, ‖(D i).ℓ z‖ < r:= by
   let s:=stashp/2; have hh:stashp<0:=by norm_num [stashp]
   have hs :s<0:=by unfold s; linarith;
   filter_upwards [K_use ht hv (d:=s) (by unfold s; linarith), sliding (M:=N) Meter.Rush.any hs r hr] with i hi hx z hz using (hi _ hz).trans ((le_abs_self _).trans_lt hx)
end Provision
end YM.Contacts.Junction
