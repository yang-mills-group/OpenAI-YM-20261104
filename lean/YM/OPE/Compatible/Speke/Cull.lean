import YM.OPE.Compatible.Speke.Fit
/-!
# Triad for cohorts. inherited contract
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
variable {U:Gloam}{d c s:ℝ}{K:ℕ→ℕ}{k j l m:ℕ}{X Y Z: Panels} {A:Zem}{p q t:Pose}
lemma voxer(x y:Tile):voice (x+y)=voice x+voice y:=by unfold voice; simp only[Pi.add_apply];ring
lemma yards (X Y:Panels)(x i a b):yard (fun a=> (X+Y) a i) x a b=yard (fun a=>X a i) x a b+yard (fun a=>Y a i) x a b:=by funext i; fin_cases i<;>rfl
lemma tab_s (X X' Y Z:Panels): Triad K A (X+X') Y Z=Triad K A X Y Z+Triad K A X' Y Z:=by
   unfold Triad; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro v _; funext i; unfold cubic; simp_rw [yards, voxer, add_mul]; exact Finset.sum_add_distrib
lemma tab_a (X Y Y' Z:Panels):Triad K A X (Y+Y') Z=Triad K A X Y Z+Triad K A X Y' Z:=by
   unfold Triad; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro v _; funext i; unfold cubic; simp_rw [yards, map_add A,LinearMap.add_apply, mul_add]; exact Finset.sum_add_distrib
lemma tab_b (X Y Z Z':Panels):Triad K A X Y (Z+Z')=Triad K A X Y Z+Triad K A X Y Z':= tab_a X Z Z' Y (A:=A.flip)
def Trig (U:Gloam)(d:ℝ)(x:Panels)(k:ℕ):Prop:= ShiftRay U d k x ∨ ∃ p:Pose, x=SinB p ∧ k=p.heat+1
def Cohort (U:Gloam)(d:ℝ)(x:Panels)(k:ℕ):Prop:= Trig U d x k ∨ ∃ a b:Panels,x=a+b ∧ Trig U d a k ∧ Trig U d b k
lemma scorch (hx:Cohort U d X k)(h:0<s)(hh:s≤ d): Cohort U s X k:= by
    have hv(X:Panels)(k:ℕ)(hp:Trig U d X k):Trig U s X k:=hp.imp (fun hx=> ⟨fun i=>(hx.ports i).slice h hh,hx.glass,hx.dull⟩) id
    obtain hx|⟨a,b,x,hp,hq⟩:=hx; exact Or.inl (hv X k hx); exact Or.inr ⟨a,b,x,hv a k hp,hv b k hq⟩ -- ..
variable (hw:Woody U K d)(hc:Vener A c)
include hw hc
lemma probus (hp:0<d)(hx:Trig U d X k)(hy:Trig U d Y j)(hz:Trig U d Z l)(hm:m+4=k+1+j+l): Fruit U m (Triad K A X Y Z) 0:=by
    obtain hx|⟨x,rfl,rfl⟩:=hx
    · obtain hy|⟨y,rfl,rfl⟩:=hy
      · obtain hz|⟨z,rfl,rfl⟩:=hz; exact never hw hm hx.ports hy.ports hz.ports; exact onceS hw hm hx.ports hy.ports
      obtain hz|⟨z,rfl,rfl⟩:=hz; rw [cubFlip]; exact onceS hw (by omega) hx.ports hz.ports; exact sacred hw hm hx hc
    obtain hy|⟨y,rfl,rfl⟩:=hy
    · obtain hz|⟨z,rfl,rfl⟩:=hz; exact onceC hw hm hy.ports hz.ports; rw [cubFlip]; exact rotor hw (by omega) hy hc.flip
    obtain hz|⟨z,rfl,rfl⟩:=hz; exact rotor hw hm hz hc; exact allC hw hp hm
lemma charity (hp:0<d)(hx:Cohort U d X k)(hy:Cohort U d Y j)(hz:Cohort U d Z l)(hm:m+4=k+1+j+l): Fruit U m (Triad K A X Y Z) 0:=by
    have he(X Y:Panels)(hx:Trig U d X k)(hy:Trig U d Y j):Fruit U m (Triad K A X Y Z) 0:=by
        obtain hh|⟨a,b,h,hp',hq'⟩:=hz; · exact probus hw hc hp hx hy hh hm
        rw [h,tab_b,← add_zero (0:ℝ)]; exact Fruit.sum (probus hw hc hp hx hy hp' hm) (probus hw hc hp hx hy hq' hm)
    have ht(X:Panels)(hx:Trig U d X k):Fruit U m (Triad K A X Y Z) 0:=by
        obtain hh|⟨a,b,h,hp,hq⟩:=hy; exact he X Y hx hh; rw [h,tab_a,← add_zero (0:ℝ)]; exact Fruit.sum (he X a hx hp) (he X b hx hq)
    obtain hh|⟨a,b,h,hp,hq⟩:=hx; exact ht X hh; rw [h,tab_s,← add_zero (0:ℝ)]; exact Fruit.sum (ht a hp) (ht b hq)
end YM.OPE.Nestle
