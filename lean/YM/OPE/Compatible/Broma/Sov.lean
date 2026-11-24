import YM.OPE.Compatible.Chain.Tug
import YM.OPE.Compatible.Broma.Brand
/-! # Operator norm Cov orientation prices -/
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
-- Op on Lap
lemma dentDiff (A B:RowB I)(m k:ℕ)(h:A.val=B.val): lapD A m k= lapD B m k:=by
    apply ContinuousLinearMap.ext; intro x; apply lilies_inj I k m; ext1 i; simp_rw [pulse_i, h]
lemma gapAura (A B C:RowB I)(m k:ℕ)(h:A.val=B.val+C.val): vibeC I m k A=vibeC I m k B+vibeC I m k C:=by -- direct seed
     apply ContinuousLinearMap.ext; intro x; apply seed_inj m (k+2) _; simp_rw [_root_.add_apply, map_add,vibe_eq,nailD,h]; ext1 i; simp [tunnel,mul_add]
lemma defies (A B C:RowB I)(m k:ℕ)(h:A.val=B.val+C.val): lapD A m k=lapD B m k+lapD C m k:=by
     apply ContinuousLinearMap.ext; intro x; funext i; erw [_root_.add_apply, Pi.add_apply]; rw [pinch,pinch,pinch, gapAura A B C m i.val h,_root_.add_apply,map_add,smul_add]
lemma stepLamp (A B:RowB I)(u:ℝ)(h:0≤u)(hp:∀ i j a,‖A.val i j a-B.val i j a‖≤u)(m k:ℕ): ‖lapD A m k-lapD B m k‖≤ wind k*u :=by
     let C:RowB I:=⟨A.val-B.val,u,h,hp⟩; have he:= defies A B C m k (show A.val = B.val + (A.val - B.val) by abel); rw [he,add_sub_cancel_left]; exact lapE ..
lemma CotWarp (v u:Train r)(h:4≤r)(X:KernelChoices)(s a:ℝ)(hp:0≤s)(ht:0≤a)(hs:(ShellRow X v-ShellRow X u).strip s a) (k m:ℕ):
     ‖lapD (atlasF G v h X) k m-lapD (atlasF G u h X) k m‖≤ wind m*((told X h).choose*Real.sqrt a):=by
          have he:= (told X h).choose_spec; have hi:0 ≤ (told X h).choose*Real.sqrt a:=mul_nonneg he.1 (by positivity); apply stepLamp _ _ _ hi; intro p q x; unfold atlasF; dsimp only; split
          next ha=>
               rw [norm_sub_rev]; let f(v:Train r):=vein v X (coord p.1) (coord q.1) x; let g(v:Train r):=fun n:ℕ=> f v (tick2 n) 0
               apply le_of_tendsto (((guessed u h (coord p.1) (coord q.1) x).sub (guessed v h (coord p.1) (coord q.1) x)).norm); exact Eventually.of_forall fun i=>he.2 u v s hp a ht hs (tick2 i) (0,coord p.1) (0+wrap (tick2 i) x,coord q.1)
          next _=>rw [sub_zero, norm_zero];exact hi
