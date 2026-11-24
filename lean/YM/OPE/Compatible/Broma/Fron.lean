import YM.OPE.Compatible.Broma.Yarrow
/-!
# Clock mapping highest origins and conjugate transports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
section retix
noncomputable def lava (G:Gauge)(k m:ℕ)(hm:1≤m) (C:KernelChoices)(v: Train r)(h:4 ≤ r)(u:ℝ):bed G k m→L[ℝ] bed G k m:=
    (puffX G m k C v h u ∘L (bed G k m).subtypeL).codRestrict _ (by intro x; cases m with | zero=>omega | succ m=> rw [ContinuousLinearMap.comp_apply, puffX, expAt]; exact lockS C v h u x.property)
noncomputable def Larix (G:Gauge)(x:Train r)(h:4 ≤ r)(C:KernelChoices)(hp: Aware d τ)(u:ℝ):Tracts G d τ →L[ℝ] Tracts G d τ:= ContinuousLinearMap.pi fun i:Phase=>lava G (d+i.val) (τ i) (le_trans (by decide: (1:ℕ)≤45) (awareLeaf hp i)) C x h u∘L ContinuousLinearMap.proj i
variable (G)(h:Aware d τ)(s:ℝ)
local notation "V!"=>Tracts G d τ
lemma lavaX (x:Train r)(ht:4≤r) (p: V!)(i:Phase):
     (Larix G x ht C h s p i).val= boostS (atlasF G x ht C) s (τ i) (d+i.val) (p i).val:= by
       exact (show puffX G (τ i) (d+i.val) C x ht s (p i).val= _ from expAt ..)
lemma blaze (x:Train r)(ht:4 ≤ r) (p: V!): Larix G x ht C h s (Larix G x ht C h (-s) p)=p:=by
     ext1 i;apply Subtype.ext; rw [lavaX,lavaX]; exact sustain ..
noncomputable def ConeZ (G:Gauge)(x:Train r)(ht:4 ≤ r)(C:KernelChoices)(hp:Aware d τ)(s:ℝ): Tracts G d τ≃L[ℝ] Tracts G d τ := {
     (Larix G x ht C hp s) with
     toFun := Larix G x ht C hp s
     invFun:= Larix G x ht C hp (-s)
     left_inv:=fun i=> by simpa only [neg_neg] using! blaze (C:=C) G hp (-s) x ht i
     right_inv:=fun i=> blaze G hp s x ht i
     continuous_toFun :=(Larix G x ht C hp s).continuous
     continuous_invFun:= (Larix G x ht C hp (-s)).continuous }
-- natural operator coordinates fixed stage
end retix
local notation "X!" => TileC T P p R b
local notation "u!" => (upperX:X!→ℝ)
local notation "q!" => (downK:X!→ℝ)
lemma saucy (hp:Crest G P K.K m)(h:Aware d τ)(s:ℝ): Brim
    (fun i:X! => Larix G (UA i).gear P.order_cut K.K h s) (fun i:X! => Larix G (VA i).gear P.order_cut K.K h s) u! fareI:=by
       have hh:1≤u!:= max_cap _ _ _ _ _; have hv: 0 ≤ (fareI:X!→ℝ):= fixedTheta; refine Wπ hh hv fun i=>?_ 
       have ht:1 ≤ τ i:=(show (1:ℕ)≤45 by decide).trans (awareLeaf h i); let A(j:X!):= lava G (d+i.val) (τ i) ht K.K (UA j).gear P.order_cut s; let B(j:X!):= lava G (d+i.val) (τ i) ht K.K (VA j).gear P.order_cut s
       have hd : Brim A B u! fareI:= brimDown (brimPuff s hp (τ i) (d+i.val)) hh hv _ _ _ (fun i j=>rfl) (fun i j=>rfl)
       convert! Canal (Brim.constant (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun i:Phase=> bed G (d+i.val) (τ i)) i)) hd hh hv using 1
lemma Brim.after {E:Type} [NormedAddCommGroup E] {X Y:TileC T P p R b→ E}(h:Brim X Y u! fareI): Brim (fun i:X! =>X (fallsF i)) (fun i:X! => Y (fallsF i)) u! fareI:=by
     have ht(f:X!→E)(Z:X!→ℝ)(hp:Wealth f u! Z)(hh:∀ i,Z (fallsF i)≤Z i):Wealth (f∘fallsF) u! Z:=by
          obtain ⟨a,H,d,D⟩:= hp; have hx:1 ≤ u!:= max_cap _ _ _ _ _; refine ⟨a,H,d,fun i=>?_⟩; exact (D (fallsF i)).trans (mul_le_mul_of_nonneg_left (hh i) (mul_nonneg H (pow_nonneg (zero_le_one.trans (hx i)) _)))
     exact ⟨ht _ 1 h.A (fun i=>le_rfl),ht _ 1 h.B (fun i=>le_rfl),ht _ fareI h.D (fun i=>by rw [fareI,fallsF]; exact pow_le_pow_of_le_one thetaC.1.le thetaC.2.le (Nat.le_succ _))⟩
end YM.OPE.Drift
