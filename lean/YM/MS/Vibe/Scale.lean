import YangMills.WilsonProof.NativeSupport.YM.MS.Dock.Recipes
/-!
# Identities of effective master expression in spectrum variables

No proof of vacuum gauging; rank.P wrappers. Contact with Pole.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F: T (Flats G)}{J N L:Flats G}{f:Coat G}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}
def park (G:Gauge): MH (Flats G):= QN G + CycleN (B0 G 0)
def bridge (G:Gauge): Signal.Pair (Flats G):= TreeN ( B0 G 0)
def Pose (n:ℕ)(t:ℂ)(X F:T ( Flats G)): Flats G:= park G (F n) + t • pairW (bridge G) X F n
abbrev PB (X:T ( Flats G)) : T (Flats G) := fun n=> Pose n ((2:ℂ)⁻¹) X X
abbrev PM (X Y:T (Flats G)) : T (Flats G) := fun n=> Pose n 1 X Y
-- spectral coupling.Poses unify scaling & Lap.
abbrev Grid (z:ℂ)(y t:ℝ)(G:Gauge): GridR (Mob G):= γ z (tenorK z y) t G
abbrev File (z:ℂ)(s y:ℝ)(h:ℕ)(F:T (Flats G)) : T (Mob G) := fun i=> Parade (F i) h y s z
-- note parameter order `File z s(log R) y`
lemma view_step (hp:Moony b J ) (h:ℕ): ∀ᶠ i in dotty,∀ s y, Parade (step0 G J) h y s i=(Grid i y s G).P ( Parade J h y s i) := by
    filter_upwards [high0,Moony.sunup (all0 hp)] with i hi hP s y; rw [step0, length_at  (n:=h) hi (heed (A_caps ..)) hP (a:=4) (by ring:(4:ℂ)-4= (h:ℂ)-h), pA]; rfl
lemma view_park (hp:Moony b J) (h:ℕ): ∀ᶠ i in dotty,∀ s y, Parade (park G J) (h+1) y s i=(Grid i y s G).J ( Parade J h y s i):= by
    filter_upwards [high0,Moony.sunup (all0 hp)] with i hi hP s y; rw [park,LinearMap.add_apply,page_add, Pi.add_apply,length_at hi (heed (B_caps ..)) hP (show (3:ℂ)-4=(h:ℂ)-(h+1:ℕ) from by push_cast; ring ),pB,Q_at]; rfl
lemma viewX (a b c:ℕ) (he:(4:ℂ)-a-b=-(c:ℂ))(z:ℂ)(s y:ℝ): Parade (pairW (drive0 G) X F n) c y s z = pairW ( Grid z y s G).X (File z s y a X) (File z s y b F) n:= by unfold drive0; simp only [paired, page_sum, Finset.sum_apply]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [ tree_at (reverse_a G 0) he,pA]; rfl
lemma viewY (a b c:ℕ) (he:(3:ℂ)-a-b=-(c:ℂ))(z:ℂ)(s y:ℝ): Parade (pairW (bridge G) X F n) c y s z= pairW (Grid z y s G).C (File z s y a X) (File z s y b F) n := by unfold bridge; simp only [paired, page_sum, Finset.sum_apply]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [ tree_at (reverse_b G 0) he, pB]; rfl
lemma masterRow (hp:Moony b (F n))(h:ℕ)(x:ℂ): ∀ᶠ i in dotty, ∀ s y, File i s y (h+1) (fun n=> Pose n x X F) n= ((promote (Grid i y s G).J ( File i s y h F)+ x • pairW (Grid i y s G).C (File i s y 4 X) (File i s y h F)) n):= by
   filter_upwards [ view_park hp h] with i hi s y; simp only [File,Pose,page_add,page_smul,Pi.add_apply,Pi.smul_apply,hi,promised]; rw [ viewY 4 h (h+1) (by push_cast; ring)] -- fails due File unfolded RHS
lemma growthB (hp:Moony b (X n))(ht:X 0=0): ∀ᶠ i in dotty,∀ s y, Parade (program G n X+step0 G (X n)) 4 y s i=(Grid i y s G).grow (File i s y 4 X) n:= by
    filter_upwards [view_step hp 4] with i hi s y; rw [ page_add, Pi.add_apply,pc_max ht,page_smul,Pi.smul_apply,viewX 4 4 4 (by ring),hi,add_comm]; rfl
lemma growthM (hp:Moony b (F n))(ht:X 0=0)(h:ℕ): ∀ᶠ i in dotty,∀ s y, Parade (platform X n F+step0 G (F n)) h y s i= (Grid i y s G).lives (File i s y 4 X) (File i s y h F) n:= by
   filter_upwards [view_step hp h] with i hi s y; rw [ page_add,Pi.add_apply, pm_max ht, viewX 4 h h (by ring),hi,add_comm]; rfl -- no page_smul
end YM.MS.Emit
