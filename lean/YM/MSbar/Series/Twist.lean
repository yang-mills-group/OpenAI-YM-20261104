import YM.MSbar.Series.Machine

/-! Dilation derivation. On propagating one level, may subtract per-grade cost of a
loop completely. Only ℓ counts shifts in momentum dimensional factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Category
open Function Finset Filter
open scoped BigOperators Classical
variable {X Y Z: Type*} [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z]

-- remember only diagonal operations needed
structure Twist (M:Machine X Y)(A:Homo X X)(B:Homo Y Y)(a:ℂ):Prop where
    vec (x:X): B (M.brst x)= M.brst (A x)
    loop (x:X): B (M.red x)+a • M.red x=M.dot x+M.red (A x)
    pairs (x:X): B (M.bracket x x)= M.splice x x+(2:ℂ)•M.bracket x (A x)
namespace Twist
def elong (c:ℂ) : Form X →ₗ[ℂ] Form X := {toFun:= fun f i=> (c * i) • f i,map_add':=fun x y=>funext fun i=>by simp [smul_add],map_smul':=fun b x=> funext fun i=> smul_comm .. }
lemma nel {i:ℕ}(c:ℂ)(x:Form X):elong c x i=(c*i) • x i:= rfl
lemma brave (c:ℂ)(B: Tree X Y Z) (x:Form X)(y:Form Y): elong c (knot B x y)= knot B (elong c x) y + knot B x (elong c y):=by
    funext n; simp only [nel, knotted, smul_sum,Pi.add_apply, ← sum_add_distrib]; apply sum_congr rfl; rintro ⟨i,j⟩ H; obtain h : i+j=n:= mem_antidiagonal.mp H; dsimp only; rw [← h]; push_cast; simp only [mul_add,map_smul,LinearMap.smul_apply,add_smul]
variable {M:Machine X Y}{A:Homo X X}{B:Homo Y Y}{a:ℂ}(hC:Calculus M)(h: Twist M A B a)(s:Bool)
def stretch (A:Homo X X)(b:ℂ):= act A + elong b
include h hC
lemma next (b:ℂ): Twist (propagate M s) (stretch A b) (stretch B b) (a-(if s then b else 0)) := by
    constructor
    · intro x; funext n; simp only [stretch,LinearMap.add_apply,act_val,Pi.add_apply,nel,propagate,map_add,map_smul,h.vec]
    · intro x; cases s
      · funext n; simp only [propagate,stretch,post,Bool.false_eq_true,↓reduceIte,act_val,map_add,map_smul,LinearMap.add_apply,Pi.add_apply,Pi.smul_apply,nel, sub_zero]; rw [add_right_comm,h.loop,add_assoc]
      funext n; cases n with
      | zero=> simp [stretch,propagate,post,nel]
      | succ n=> simp only [propagate,stretch,post,↓reduceIte,sea_pos,act_val,map_add,map_smul,LinearMap.add_apply,Pi.add_apply,Pi.smul_apply,nel]; rw [← add_assoc,← h.loop]; push_cast; module
    intro x; have e: act B (knot M.bracket x x) = knot M.splice x x+ (2:ℂ) • knot M.bracket x (act A x):= by
        funext n; let H:=Pitch.ish_pitch n x; exact Pitch.eq ((H.knot H M.bracket).points B) ((H.knot H M.splice).add ((H.knot (H.points A) M.bracket).scale 2)) (fun c=> h.pairs (ish n x c))
    simp only [propagate,stretch,LinearMap.add_apply,brave,e,map_add,smul_add]; rw [(show knot M.bracket (elong b x) x=knot M.bracket x (elong b x) from (Calculus.next hC s).sk ..),add_assoc,two_smul,two_smul]
end Twist
end YM.MSbar.Category
