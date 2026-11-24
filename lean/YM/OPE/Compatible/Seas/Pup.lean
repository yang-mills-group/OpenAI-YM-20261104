import YM.OPE.Compatible.Seas.Illu
/-!
# Elementary curl leg
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis Balsam -- Port not visible first
open scoped BigOperators Classical ContDiff
structure Pose where
   m: List Axis
   a:Axis
   b:Axis
   x:Cover
namespace Pose
open Balsam Port
variable {n:Side}{U:Gloam}{z:(i:ℕ)→ Site (U.M i)}{d:ℝ}{t:Axis→ℕ→Cover→ℝ}(p:Pose)
def heat :ℕ:=p.m.length+2 -- field
-- Polar.T axis coefficient.Insert smearing
variable {E:Type*} [AddGroup E]
def Lck (f:Axis→E)(i:Axis):E:= (if i=p.b then f p.a else 0)-(if i=p.a then f p.b else 0)
def ray (D: List Axis→Cover→ℝ)(i:Axis)(x:Cover):ℝ:= p.Lck (fun a=>D (a::p.m) (x+p.x)) i
def icicle (i:Axis):= p.ray hull i
def pureD (l:List Axis)(i:Axis): E4→ℝ:=p.Lck (fun a=>tint (l++a::p.m)) i
lemma dips (i:Axis)(x:Cover)(l): dvol l (p.icicle i) x= p.ray (fun q=> hull (l++q)) i x:=by -- I
    induction l generalizing x with
    | nil=>simp [dvol,icicle]
    | cons a l ih=>rw [dvol]; unfold numDiff; rw [ih,ih]; unfold ray Lck; simp only [List.cons_append,hull]; rw [show stint a=(step a:Cover) from rfl, add_right_comm x]; split_ifs <;> abel
lemma era (l:List Axis)(i):Quip ((↑(p.heat+1+l.length:ℕ):ℤ)) (dvol l (p.icicle i)) (p.pureD l i):=by
    rw [funext fun x=> p.dips i x l]
    let X(i):=fun x=> hull (l++i::p.m) (x+p.x)
    let B(i):=tint (l++i::p.m)
    have hp(j): Quip (↑(p.heat+1+l.length:ℕ)) (X j) (B j):=by rw [show p.heat+1+l.length=(l++j::p.m).length+2 from by simp [heat];omega]; exact (lineQ _).shiftP _
    have he : (p.ray (fun q=> hull (l++q)) i)= (if i=p.b then X p.a else 0)-(if i=p.a then X p.b else 0):=by funext v; unfold ray Lck X; split_ifs <;>rfl
    rw [he]; unfold pureD Lck; have ho(k:ℤ) : Quip k (0:Cover→ℝ) (0:E4→ℝ):=fun n x h p hp ht=>by simp [quilting]
    apply qt_sub; split_ifs; exact hp _; apply ho;split_ifs; exact hp _; apply ho
where qt_sub {k:ℤ} {f g:Cover→ℝ}{F G:E4→ℝ}(h:Quip k f F)(hd:Quip k g G):Quip k (f-g) (F-G):=by intro n x hn p hp ht; simpa only [quilting,Pi.sub_apply, mul_sub] using! (h n x hn p hp ht).sub (hd n x hn p hp ht)
-- regular.PEAK.PORT
private def cuffX (f:Axis→ℕ→Cover→ℝ)(i:Axis):ℕ→Cover→ℝ:=p.Lck f i
def cuff (g:List Axis→ℕ→Cover→ℝ)(q:Axis):ℕ→Cover→ℝ:= p.cuffX (fun i=>shutter p.x (g (i::p.m))) q
private lemma cuff_tray {g:List Axis→ℕ→Cover→ℝ}(hr:0<d)(hf:∀ i:Axis, Port U d (p.heat+1) (g (i::p.m)))(hg:∀ i:Axis, Hum (g (i::p.m))) (hx:∀ i, g (i::p.m)=smear i (g p.m)): ShiftRay U d (p.heat+1) (p.cuff g):=by
    let G(i:Axis):=shutter p.x (g (i::p.m)); have he(i):Port U d (p.heat+1) (G i):= (hf i).pass _; have H(i):Hum (G i):=hum_pass (hg i) _; constructor
    · intro a; change Port _ _ _ (_-_); rw [sub_eq_add_neg]; apply glue _ (neg_s _); split_ifs; apply he; exact nullC hr; split_ifs; apply he;exact nullC hr
    · intro a; change Hum (_-_); apply hue_minus; split_ifs; apply H; exact hue_zero;split_ifs; apply H; exact hue_zero
    refine fun x=> Eventually.of_forall (fun i=>?_); have hT(a:Axis)(v:Cover):p.cuff g a i v= ((if a=p.b then G p.a i v else 0)-(if a=p.a then G p.b i v else 0)):=by unfold cuff cuffX Lck G; split_ifs<;>rfl
    simp_rw [Finset.sum_apply]; unfold smear numDiff; simp_rw [hT]; rw [Finset.sum_sub_distrib]; simp [Finset.sum_sub_distrib]; unfold G shutter; simp_rw [hx,smear,numDiff]; rw [add_right_comm x, add_right_comm x (stint p.a) _, add_right_comm (x+p.x)];ring
lemma cuff_far (h:Drone U z)(hp:z 0≠0):ShiftRay U (seaRise U z 0) (p.heat+1) (p.cuff (fun D=> ebb D U z)):=p.cuff_tray (sea_pos hp) (fun i=>shores (i::_) h hp) (fun i=>ebb_h h hp _ (by simp)) (fun i=>ebb_a ..)
lemma cuff_pin (h:∀ᶠ i in atTop,Even (U.M i).val):ShiftRay U (1/2) (p.heat+1) (p.cuff (fun D=> flood D U)):=p.cuff_tray (by norm_num) (fun i=>pegs (i::_) h) (fun i=>flood_h U _ (by simp)) (fun i=>flood_a ..)
end Pose
end YM.OPE.Nestle
