import YM.MS.ScaleForest.Iron
import YM.MS.ScaleForest.PressedFour
import YM.MS.ScaleForest.LineSums
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-!
# Physical tests in the placement recursion

Derivation of the gluing formulas for *sums over the actual graph palette*.
Specialize only after reconstruction of all Laurent cancellations at
connected children, so `projectV` readout will be used on the chart at
z=0 of a regularized/holomorphically extended term/repaired family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect High Latch Job Rake Rake.Geo Tone Momentum Osc Snap Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} {z:ℂ} {X Y : Curtain G I}

-- sum over the full Ripe palette
private lemma aroundSum {V:List (LineRule G)} : Knot false (V.map LineRule.half).sum:= by induction V with| nil=> exact Knot.zero | cons i l ih=> exact (i.ok.forms false).add ih
private lemma lineLeft {X : Mob G} (h:Form0 false X) (hv:z∈Town) (V:List (LineRule G)) : ocean z (V.map LineRule.half).sum X = (V.map (fun i=> ocean z i.half X)).sum := by
   induction V with
   | nil=> exact (by simp only [List.map_nil,List.sum_nil]; simpa only [zero_smul] using scaleL (U:=0) (i:=z) Knot.zero h 0)
   | cons i l ih=> rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,oceanL (i.ok.forms false) h aroundSum hv,ih]
private lemma closeLeft {X : Mob G} (h:Form0 false X)(hv:z∈Town) (V:Palette G) (μ:ℝ) : (V.lines.map (fun i=> closeG i.half z μ X)).sum= closeG (fullShell G).half z μ X:= by
   simp_rw [closeG_eq]; simp only [fullShell]; rw [← V.quality,lineLeft h hv]; generalize V.lines=l; induction l with| nil=>simp| cons i l ih=> simp only [List.map_cons,List.sum_cons, smul_add,ih]
private lemma bridgeLine_t (F H:Mob G) (V:Palette G) : (V.lines.map (fun p=> bridgeG p.half F H)).sum=bridgeG (fullShell G).half F H:= by
   simp_rw [show ∀ K:LineRule G, bridgeG K.half F H=arbor K.half F H from fun i=>bridgeG_eq i.ok.rev ..]; simp only [fullShell]; rw [← V.quality]; generalize V.lines=l; induction l with
   | nil=> simp only [List.map_nil,List.sum_nil]; simpa only [zero_smul] using (down_leg (0:Rip G) 0 F H).symm
   | cons i l ih=> simp only [List.map_cons,List.sum_cons,two_leg,ih]
private lemma pinLeft {X Y:Mob G}(hx:Form0 false X)(hy:Form0 false Y) (hv:z∈Town) (V:Palette G)(A:QP)(y:ℝ) :
    (V.lines.map (fun K=> pinned K.half z y A X Y)).sum=pinned (fullShell G).half z y A X Y := by
   simp_rw [ show ∀ K:LineRule G,pinned K.half z y A X Y= tenorK z y • sweptRef z K.half (rephase A X) Y from fun K=> placedEq (K.ok.forms false) K.ok.even K.ok.rev hx hy hv A y]; obtain hV:= form_rephase hx A
   simp only [fullShell]; rw [← V.quality]; generalize V.lines=l;
   induction l with
   | nil=>
      unfold sweptRef; rw [ List.map_nil,List.map_nil,List.sum_nil,List.sum_nil ];
      have H (F:Mob G) (h:Form0 false F): ocean z 0 F=0:= lineLeft h hv [];
      rw [ H _ (form_weave hV hy), H _ hV, H _ hy ]; unfold weave; simp only [Pi.zero_apply,map_zero, LinearMap.zero_apply]; change 0=tenorK z y • ((0:Mob G)-0-0); simp
   | cons i l ih=>
      have hh(f g:Mob G): weave (f+g) Y=weave f Y + weave g Y:= funext fun i=> map_add ((product (field parity)).flip (Y i)) (f i) (g i)
      have hp(f g:Mob G): weave (rephase A X) (f+g)= weave (rephase A X) f+ weave (rephase A X) g:= funext fun i=> map_add ..
      rw [ List.map_cons, List.map_cons,List.sum_cons,List.sum_cons,ih ];
      unfold sweptRef; obtain Q:=i.ok.forms false; rw [oceanL Q (form_weave hV hy) aroundSum hv,oceanL Q hV aroundSum hv,oceanL Q hy aroundSum hv,hh,hp]; rw [← smul_add]; congr 1; abel

-- invocation at reference momentum charts.
def projectV (a:ℂ) : Curtain G I→ₗ[ℂ] Glade G I where
   toFun X i t := backing a X 0 t i 0
   map_add' F H:= funext fun i=>funext fun t=> congr_fun (map_add ( plower a t) (F 0 t i) (H 0 t i)) 0
   map_smul' c F:= funext fun i=>funext fun t=> congr_fun (map_smul (plower a t) c (F 0 t i)) 0
lemma projects (a:ℂ) {X Y:Curtain G I} (h : X 0=Y 0) : projectV a X=projectV a Y:= by funext i t; change plow a t (X 0 t i) 0=plow a t (Y 0 t i) 0; rw [h]
lemma VertRiver (X:Curtain G I) : projectV 0 (vertical X)= Job.river (projectV 0 X):= by funext i t; change backing 0 _ _ _ _ 0=_; rw [backingVert]; rfl

def Seen (F:Curtain G I) : Prop:=∀ i t, Form0 false (F 0 t i)
lemma Seen.zero : Seen (0:Curtain G I) := fun _ _=> Form0.zero
lemma Seen.add (hf:Seen X)(hh:Seen Y): Seen (X+Y):= fun i t=> (hf i t).add (hh i t)
lemma Seen.list {l : List (Curtain G I)} (h:∀ i∈l,Seen i) : Seen l.sum := by induction l with| nil=> exact Seen.zero | cons i l ih=> exact ( h i (by simp)).add (ih (fun i hi=> h i (List.mem_cons_of_mem _ hi)))

variable (V:Palette G)(μ:ℝ) (hX:Seen X) (hY:Seen Y)
local notation "D"=> constantP G I (PlanetD G)

lemma primary (G:Gauge)(I: Type) (v:I) (t:ℝ) : constantP G I (PlanetD G) v t= Alps.pulse 4 t (A0 G 0) 0:= by rw [pA]; rfl
lemma sum_day {J:Type} (L:List J) (f:J→ Curtain G I) (z:ℂ) (t:ℝ)(i:I) : (L.map f).sum z t i=(L.map (fun x=> f x z t i)).sum:= by induction L with| nil=> rfl| cons j L ih=> simp only [List.map_cons,List.sum_cons, Pi.add_apply, ih]
lemma pit : (0:ℂ)∈Town:=by simpa using Town_nat 0

include hX
theorem sensingUfull : projectV 0 (Ufor (fullShell G) μ X) = sailP (fun _=> planeF) D (projectV 0 X):= by
   funext i s; let F:= fullShell G; obtain hk:= F.ok.forms false; change plow 0 s (closeG F.half _ _ (X 0 s i)) 0=cycle ( D i s) _ _; rw [ ← closure_meter hk (hX i s) s μ 0 0, actual_cycle (fze hk _ _) (fseed (hX i s) _ _), primary ]; rfl
lemma palU : (V.lines.map (fun K=> Ufor K μ X)).sum 0= Ufor (fullShell G) μ X 0:= by
   funext t i; rw [sum_day]; exact closeLeft (hX i t) pit V _
lemma sensingU : projectV 0 (V.lines.map (fun K=> Ufor K μ X)).sum = sailP (fun _=>planeF) D (projectV 0 X) := Eq.trans (projects 0 (palU V μ hX)) (sensingUfull μ hX)
include hY
lemma sensingPfull (A:I→QP) : projectV 0 (Pfor (fullShell G) μ X Y A)= regionC (fun _=>planeF) A D (projectV 0 X) (projectV 0 Y) := by
   funext i s; let F:= fullShell G; let Q:= F.ok; let L:= Q.forms false; change plow 0 s (pinned F.half 0 _ _ _ _) 0=Cabin _ _ _ _ _;
   have h := pinned_meter L Q.even Q.rev (hX i s) (hY i s) pit s μ 0 0 (A i); rw [zero_add] at h; rw [← h, actual_cabin (fze L _ _) (pulsed_closed Q.even _) (a_rev _ _ Q.rev) (fseed (hX i s) _ _) (fseed (hY i s) _ _)]; congr 1; exact (primary G I i s).symm
lemma palP (A:I→QP) : (V.lines.map (fun K=> Pfor K μ X Y A)).sum 0=Pfor (fullShell G) μ X Y A 0 := by
   funext t i; rw [sum_day]; exact pinLeft (hX i t) (hY i t) pit V _ _
lemma sensingP (A:I→QP) : projectV 0 (V.lines.map (fun K=> Pfor K μ X Y A)).sum=regionC (fun _=>planeF) A D (projectV 0 X) (projectV 0 Y):= Eq.trans (projects 0 (palP V μ hX hY A)) (sensingPfull μ hX hY A)
omit hX hY
lemma sensingBfull (X Y:Curtain G I): projectV 0 (Bfor (fullShell G) X Y)=expJ D (projectV (-4) X) (projectV 0 Y):= by funext i t; change backing _ _ _ t i 0=_; rw [behind_b_for,bridgeG_eq (a_rev _ _ (fullShell G).ok.rev)]; unfold expJ; rw [primary]; rfl
lemma palB (X Y:Curtain G I): (V.lines.map (fun K=> Bfor K X Y)).sum 0=Bfor (fullShell G) X Y 0:= by funext t i; rw [sum_day]; exact bridgeLine_t _ _ _
lemma sensingB (X Y:Curtain G I) : projectV 0 (V.lines.map (fun K=> Bfor K X Y)).sum=expJ D (projectV (-4) X) (projectV 0 Y):= Eq.trans (projects 0 (palB V X Y)) (sensingBfull X Y)
end YM.MS.ScaleForest
