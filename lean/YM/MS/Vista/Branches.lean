import YM.MS.Vista.Bunker
/-!
# Difference progress Step κ. Bulk motions and rate bookkeeping also for single marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E W : Type}{M:Visa I}{P:Belt I}{F H X Y:Glade G I}{ Z:Lin I}
   {L:I→Side}{c b:Bool}{K V: Planet G I}{x y z:P.time→ℝ}{ B C:Rake.Site G I}{Q:ℕ→I→Law G}
local notation "Μ"=> Mid M L
local notation "Ω"=> enterV L b
-- cost.r4
lemma cashP (p:P.time)(x y z:P.time→ℝ): positive P.price 4 z ( rateS P 4 *x*y ) p= z p*x p*y p:= by rw [positive]; simp only [Pi.mul_apply,rateS,zpow_neg]; rw [show P.price.length p ^ (4:ℤ) = P.price.length p ^ (4:ℕ) from rfl]; field_simp [(P.price.pos p).ne']
lemma step_acc (h:Piece Μ K 1)(ht:stepOne M L K V){x y:(Μ).time→ℝ}(hx:WarpHere true true Μ X ( rateS Μ 4 ))(he:WarpHere true true Μ (X-Y) ( rateS Μ 4 * x )) ( hF:WarpHere c true Μ H y )( hY:WarpHere c true Μ (F-H) (y*x))(hm:nn y)(hq:nn x): HandC c false Μ ( expJ K X F - expJ V Y H ) (y*x):= by
    have hζ:= h false; let P:=Mid M L; let U:=Prune P false K; unfold HandC Here; rw [map_sub]; rw [show plug (J:=P.slot) ( bend G I ( expJ K X F )-bend G I (expJ V Y H))= plug (bend G I (expJ K X F))-plug ( bend G I (expJ V Y H)) from rfl,expP, expP ]; rw [ ← χ_same ht ]; rw [stepwise]; apply Lease.plus
    · unfold WarpHere at he; rw [map_sub] at he; apply Lease.sticks ( trunks hζ.cost.1 he hF ( fun _=>zero_le_one ) ( joy ( rateC _ _ ) hq ) hm ); intro i; rw [cashP]; dsimp only [Pi.mul_apply]; rw [Pi.one_apply, one_mul,mul_comm]
    unfold WarpHere at hY; rw [map_sub] at hY; apply Lease.sticks ( trunks hζ.cost.1 hx hY ( fun _=>zero_le_one ) ( rateC _ _ ) ( joy hm hq ) ); intro i; rw [ ← mul_assoc _ y x,cashP ]; simp [mul_comm]
lemma step_F (hx:WarpHere true true P X (rateS P 4))(he:WarpHere c true P F x)(hp:Piece P K y)(hq:nn x)(hv:nn y): HandC c false P ( expJ K X F ) ( y*x ) := by
    unfold HandC Here; rw [expP]; apply Lease.sticks ( trunks ( hp false |>.cost.1 ) hx he hv ( rateC _ _ ) hq ); intro p; rw [ ← one_mul x,mul_comm (1:P.time→ℝ) x,← mul_assoc,cashP ]; simp
lemma beauty (hx: HandC c b P X x)(hp: HandC c b P Y x): HandC c b P (X+ Y) x:= by unfold HandC; rw [map_add]; exact Lease.plus hx hp
lemma fancy (hx:HandC c b P X x) (u:ℂ): HandC c b P ( u • X ) x:= by unfold HandC; rw [map_smul]; exact Lease.cash u hx
lemma Cuba (Z:Finset E){X:E→Glade G I}(hf:nn x)(hp:∀ i∈ Z,HandC b c P ( X i ) x): HandC b c P (∑ i∈ Z,X i) x:= by unfold HandC; rw [map_sum]; exact He_here _ hp hf
lemma τ0 : τ 0=0:= by simp [ Vista.τ ]
lemma no_credit (a:I→ℝ)(hv:nn x)(hm:∀ i,X i (τ (a i))=0): Lease b c P.price (LaunchF P a (warp0 G I X)) x:= by
    rw [show LaunchF P a (warp0 G I X)=0 from funext fun i=> hm i.1 ]; exact Lease.zero hv
-- difference used for comparison of both unmarked/marks.Budget uniform.Need Tip.Bind helper.
lemma steered (F H X Y Z Z':Glade G I)(hx:LookS (warp0 G I X) (bend G I (F+H)))(hy:LookS (warp0 G I Y) (bend G I (Z+Z'))) : LookS (warp0 G I ( X-Y )) (bend G I ( ( F-Z )+( H-Z' )) ):= by rw [ ← add_sub_add_comm,map_sub,map_sub ]; exact look_sub hx hy
lemma live_g (hp:Glow K)(he:∀ i,Knits ( B i ))(hS:Script Z K Q B){n:ℕ}(hn:0<n): LookS (warp0 G I ( B n )) (bend G I (C_wind K Z B n)) := hooked ( he n|>.1 ) ( ( knit_plus ( LiftE.knit ( clickE _ _ hp ) ( he n )) ( knit_smul ( knit_sum _ fun _ _=> knit_tree hp ( he _ ) ( he _) ) _ ) ) |>.1 ) (hS.2 n hn |>.2) -- inference
end YM.MS.Vista
