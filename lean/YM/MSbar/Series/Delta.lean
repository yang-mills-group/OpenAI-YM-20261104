import YM.MSbar.Series.Twist
/-! BV insertion identity. Only linearized propagation; no assumptions about path integral/e.o.m.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Category
open Function Finset Filter
open scoped BigOperators Classical
variable {X Y Z: Type*} [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z]

-- ℏ is implicit in the casts: every loop contraction is shifted accordingly in the scene
namespace Calculus
def current (M:Machine X Y)(x:X):= M.white x - (2:ℂ)⁻¹ • M.bond x x
def anomaly (M:Machine X Y)(x:X):= M.brst x+ (2:ℂ)⁻¹ • M.bracket x x - M.red x
def update (M:Machine X Y)(x:X):Homo X Y:= M.brst + M.bracket x-M.red
def explicit (M:Machine X Y)(x:X):=(2:ℂ)⁻¹ • M.splice x x - M.dot x
variable {M:Machine X Y}{A:Homo X X}{B:Homo Y Y} (h:Calculus M)(ht:Twist M A B 0)
include h
lemma check (x:X): update M x (current M x)+explicit M x= M.blue (anomaly M x)- M.mix x (anomaly M x):=by
   have H:=h.tandem x
   simp only [update,anomaly,current,explicit,LinearMap.sub_apply,LinearMap.add_apply,map_add,map_sub,map_smul,h.leap,h.checkpoint,h.third,h.commute]
   -- target blue bracket term rewrite H
   rw [eq_sub_of_add_eq H]; module
include ht
lemma alive (x:X): B (anomaly M x) = M.blue (anomaly M x)- M.mix x (anomaly M x) + update M x (A x-current M x):= by
   rw [← check h]; unfold update anomaly explicit; rw [map_sub, map_add, map_smul]; have he:= ht.loop x; simp only [ht.vec,ht.pairs,LinearMap.add_apply,LinearMap.sub_apply, map_sub,show B (M.red x)= M.dot x+M.red (A x) from (by simpa using he)]; module
end Calculus
end YM.MSbar.Category
