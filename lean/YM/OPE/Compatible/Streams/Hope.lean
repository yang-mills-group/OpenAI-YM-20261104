import YM.OPE.Compatible.Streams.Brook
/-!
# Sap.EOM radical membership at launch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}{R:Patch}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier Hark
variable {u d s r l k m:ℕ}{W I E:Type}{τ:Phase→ℕ}
variable {K:Sponsor G}{S:Seasons K}{t:ℝ}(A: Alps K S s t)(hr:LocalRatio P)(hp:4 ≤ s)(hs:G.Simple)(hv:0 ≤ t)(R:Patch){n:Side}(x y:Site n)(H:Even n.val)
local notation "M!"=> CountL n R.L
local notation "Y!"=> solar G d τ
noncomputable abbrev BitA (i:Phase)(j:ℕ): Dice (solar G d τ):= ArmZ A (spikeS K R x j) (spikeS K R y j) (evenBoot K R H j) hs hp hr hv i
lemma BitSeq (p q:Y!)(i:Phase)(j:ℕ):BitA A hr hp hs hv R x y H i j p q=(WQ (P:=P) (R:=R) A hp hs x y H p q j).seq i.val:= lanceZ ..
open Quit.Jac
local notation "μ"=> lapPrice (Patch.L R) l
abbrev RQuiet (l:ℕ)(p:Y!):Prop:=∀ (n:Side)(x y:Site n)(H:Even n.val),Pins K R x y→∀ i (q:Y!),Thick (lapPrice R.L l*lapPrice R.L l) (fun j=> BitA A hr hp hs hv R x y H i j p q)
noncomputable def MainSap(l:ℕ):Submodule ℝ (solar G d τ) where
    carrier:={x|RQuiet A hr hp hs hv R l x}
    zero_mem':= fun _ x y H _ i q=>by simp only [map_zero,_root_.zero_apply]; have hx:0 < lapPrice R.L l:= EndFare ..; exact Thick.hex ⟨0,(Hex.zero ℝ 0)⟩ le_rfl (mul_pos hx hx)
    add_mem':=fun {x y} hx hy n a b H h i q=>by simp only [map_add,_root_.add_apply]; exact Thick.add (hx n a b H h i q) (hy n a b H h i q)
    smul_mem':=fun c x hx n a b H h i q=>by
          simp only [map_smul,_root_.smul_apply]; obtain ⟨m,hm,hv,c',hc'⟩:= (hx n a b H h i q).Bill; exact Thick.hex ⟨_, hc'.tint c⟩ hm hv
lemma minor (p:solar G d τ)(h: p∈ MainSap A hr hp hs hv R (l:=l))(hz:Aware d τ): trellisA G hz p∈MainSap A hr hp hs hv R (l:=l):=by
     rintro n x y H he i q; let B:=fun i:Phase=> (fun j:ℕ=> BitA A hr hp hs hv R x y H i j p q); let U:=fun i:Phase=>(fun j:ℕ=>BitA A hr hp hs hv R x y H i j (trellisA G hz p) q); let f(j:ℕ):Token:= WQ (P:=P) (R:=R) A hp hs x y H p q j; have hp'(i j):U i j=(Ū*f j).seq i.val:=by
         unfold U; rw [BitSeq]; exact congr_arg (fun x:Token=>x.seq i.val) (Jac.reckoning hr hs hz ..)
     have he'(i j): B i j=(f j).seq i.val:=BitSeq ..
     change Thick (μ*(μ)) (U i); fin_cases i
     · change Thick _ (U 0); rw [show U 0=0 from funext fun i=>(hp' 0 i).trans (boneS _)]; exact Thick.hex ⟨0,Hex.zero _ 0⟩ le_rfl (mul_pos (EndFare ..) (EndFare ..))
     · change Thick _ (U 1); rw [show U 1=B 0 from funext fun i=>(hp' 1 i).trans ((boneL _).trans (he' 0 i).symm)]; exact h _ _ _ H he _ _
     change Thick _ (U 2); rw [show U 2=B 1 from funext fun i=>(hp' 2 i).trans ((boneH _).trans (he' 1 i).symm)]; exact h _ _ _ H he _ _
-- prim module for all arcs.Signal
end YM.OPE.Variance
