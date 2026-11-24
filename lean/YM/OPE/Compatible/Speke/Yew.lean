import YM.OPE.Compatible.Speke.Syrup
/-!
# Basket modes
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
open Pose (epic)
-- x points back at the mask, thus p+t steps negative
abbrev Tile := Fin 4→ℝ
abbrev Zem := Tile→ₗ[ℝ] Tile→ₗ[ℝ]ℝ
def voice (t:Tile):ℝ:= t 0+t 1-t 2-t 3
def basePair {X:Type*}(x y:X):Fin 4→X:=![x,y,x,y]
def yard {E:Type*}(f:Axis→Cover→E) (x:Cover)(i j:Axis): Fin 4→E:=![f i x,f j (x-step i),f i (x-step j),f j x]
abbrev Panels := Axis→ℕ→Cover→ℝ
abbrev cubic (R:ℕ→ℕ)(J:Zem)(F G H: Panels)(a b:Axis)(n:ℕ):ℝ:= ∑ x∈pod (R n), voice (yard (fun i=>F i n) x a b)*J (yard (fun i=>G i n) x a b) (yard (fun i=>H i n) x a b)
def Triad (R:ℕ→ℕ)(J:Zem)(F G H:Panels):ℕ→ℝ:=∑ v:PlaqAxes, cubic R J F G H v.val.1 v.val.2
abbrev SinB (p:Pose):Panels:=fun i _=>p.icicle i
-- Tunnel transport
variable {U:Gloam}{d:ℝ}{g:Panels}{p:Pose}{k j:ℕ}
def plume (g:Panels)(a b:Axis)(s:Fin 4)(n:ℕ)(x:Cover):= yard (fun i=>g i n) x a b s
def dart (g:Panels)(a b:Axis)(n:ℕ)(x:Cover):= voice (yard (fun i=>g i n) x a b)
lemma dart_eq {f:Axis→Cover→ℝ}(x:Cover)(a b:Axis): voice (yard f x a b)=numDiff b (f a) (x-step b)-numDiff a (f b) (x-step a):=by
    change f a x+f b (x-step a)-f a (x-step b)-f b x=(f a (x-step b+step b)-_) - (f b (x-step a+step a)-_); rw [sub_add_cancel,sub_add_cancel];ring
lemma port_minus {f g':ℕ→Cover→ℝ}(hf:Port U d k f)(hg:Port U d k g'):Port U d k (f-g'):=by rw [sub_eq_add_neg]; exact hf.glue hg.neg_s
lemma plant (a b)(hp:∀ i, Port U d k (g i)):Port U d (k+1) (dart g a b):=by
   rw [show dart g a b= shutter (-step b) (smear b (g a))-shutter (-step a) (smear a (g b)) from funext fun i=>funext fun x=>dart_eq x a b]; exact port_minus (((hp a).split b).pass _) (((hp b).split a).pass _)
lemma drop_top (a b j)(hp:∀ i, Port U d k (g i)): eve U (k+1) j (dart g a b)=Pose.TauS (fun i=>eve U k (j+1) (g i)) a b:=by
    let t(i):=g i; let f:=shutter (-step b) (smear b (g a)); let l:=shutter (-step a) (smear a (g b)); have hb:= (hp a).split b; have ha:= (hp b).split a; have he:dart g a b=f-l:=funext fun i=>funext fun x=>dart_eq x a b
    rw [he,sub_eq_add_neg, eve_plus (hb.pass _) ((ha.pass _).neg_s), neg_e (ha.pass _),← sub_eq_add_neg]; rw [eve_pass hb,eve_pass ha]; unfold Pose.TauS; rw [ee_a,ee_a]
lemma pull_top (a b j s)(hp:∀ i,Port U d k (g i)): eve U k j (plume g a b s)= (basePair (eve U k j (g a)) (eve U k j (g b))) s:=by
    fin_cases s; · rfl
    · exact eve_pass (hp b) (-step a)
    · exact eve_pass (hp a) (-step b)
    rfl
lemma parcelC (a b s)(hp:∀ i, Port U d k (g i)):Port U d k (plume g a b s):=by
   fin_cases s; · exact hp _
   · exact (hp b).pass (-step a)
   · exact (hp a).pass (-step b)
   exact hp _
abbrev nuF (p:Pose) := p.aLen []
lemma nu_shape (p:Pose): nuF p+2=p.heat+1:=by unfold nuF Pose.aLen Pose.heat; simp only [List.length_nil];omega
lemma lettr (p:Pose)(a b s): Nook (nuF p) (plume (SinB p) a b s 0) (basePair (p.pureD [] a) (p.pureD [] b) s):=by
   have he(i):Nook (nuF p) (p.icicle i) (p.pureD [] i):=Nook.gnaws p [] i
   fin_cases s; · exact he _
   · exact (he b).frosh (-step a)
   · exact (he a).frosh (-step b)
   exact he _
lemma lettr_step (p:Pose)(a b): Nook (nuF p+1) (dart (SinB p) a b 0) (p.OmegaS a b):=by
   have he(i a:Axis): Nook (nuF p+1) (fun x:Cover=>numDiff a (p.icicle i) (x-step a)) (p.pureD [a] i):=by
       rw [show nuF p+1=p.aLen [a] from by unfold Pose.aLen nuF; simp only[Pose.aLen,List.length_cons,List.length_nil];omega]; exact (Nook.gnaws p [a] i).frosh (-step a)
   rw [show dart (SinB p) a b 0=(fun x=>numDiff b (p.icicle a) (x-step b))-(fun x=>numDiff a (p.icicle b) (x-step a)) from funext fun x=>dart_eq x a b]; exact (he _ _).sublet (he _ _)
end YM.OPE.Nestle
