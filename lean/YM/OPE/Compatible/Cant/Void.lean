import YM.OPE.Compatible.Cant.Villa
/-!
# First components in the complement of the ghost submodule

`YM.OPE.Stroke.Bals.topArch` puts the discrepancy between the original first component and its reduced readout in the grade's `Ghost` submodule.
Since the selected subspace is disjoint from `Ghost`, `Bals.headLift` transfers a scalar relation between original first components to their reduced readouts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
variable {uα:I→ℝ}{A:(v:I)→Alps K T j (uα v)}
local notation "μ"=>lapPrice (Patch.L P)
section
variable (hX: Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
variable {ht:4 ≤ j}{hz:1≤uα}{U':Z.Ω I uα}
variable (he: Z.Floss A U' ht (le_trans zero_le_one hz) k Hp a)(f':Tracts G d τ→L[ℝ] Tracts G d τ) (i':M)(j':I)
local notation "AC"=> Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f'
local notation "CΓ"=>Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) j'
-- The reduction leaves a discrepancy in the ghost submodule.
set_option maxHeartbeats 200000 in
lemma Bals.topArch {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ)(e:J!)(x:Mint Z e.val): UΦ Z e.isLt x 0- (κ e x 0).val∈ Ghost G l e.val:=by
      let V:=κ e x; let q:= Plato Z e.val (A' e.val) e.isLt V; have ht:x-q∈ Dross Hp Z a e.val:= C.tricks e|>.slice _; have hh:=C.shares e |>.kill (x-q) ht 0 (fun _ h=> by exact False.elim ((not_lt.mpr (Fin.zero_le _)) h)); change UΦ Z e.isLt (x-q) 0∈ Ghost G l e.val at hh; rw [phiSub, ← show (κ e x 0).val=UΦ Z e.isLt q 0 from (Mway (E:=↥(Fruition Z.station (lapPrice P.L e.val))) (F:=Bead G l e.val) (BoxesΦ Z e.val e.isLt) V 0)] at hh; exact hh
-- Disjointness makes a representative in the complementary subspace unique.
private lemma equalComplementHeads {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y : Submodule ℝ E} (disjoint : Disjoint Y X) (a b : X) (p : ℝ) {x z : E}
    (ha : x - (a : E) ∈ Y) (hb : z - (b : E) ∈ Y) (h : x = p • z) : a = p • b := by
  subst x
  have hdiff := Y.sub_mem (Y.smul_mem p hb) ha
  rw [smul_sub] at hdiff
  have hY : (a : E) - p • (b : E) ∈ Y := by
    rw [show (a : E) - p • (b : E) = (p • z - p • (b : E)) - (p • z - (a : E)) by abel]
    exact hdiff
  apply Subtype.ext
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp disjoint _ hY
    (X.sub_mem a.property (p • b).property))

set_option maxHeartbeats 200000 in
lemma Bals.headLift {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ)(e:J!)(x z:Mint Z e.val) (p:ℝ)(h: UΦ Z e.isLt x 0 = p • UΦ Z e.isLt z 0) : κ e x 0= p • κ e z 0:=by
  exact equalComplementHeads (C.shares e).decmp.disjoint (κ e x 0) (κ e z 0) p
    (Bals.topArch Hp Z a C e x) (Bals.topArch Hp Z a C e z) h
-- The scalar relation holds at every grade.
end
end YM.OPE.Stroke
