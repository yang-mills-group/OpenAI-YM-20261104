import YM.X.Fill.Seed
import YM.X.Plate.Brick
/-!
# H height Charge for ∗Lie poly adaptive family∗ in units Strong. Root and vertex ink. Only literal contact jets in copied sector. no decrease assumption.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Friend
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension LatticePT MeasureTheory Metric Filter Set Function Asymptotics Reed Braid Fielding Haze Clove Interval CellsInt Shelf Size Print Crystal
open Ocean Plate
open Stems hiding X
open scoped Topology ContDiff Classical BigOperators
variable {q:ℕ+}(hq:1<q.val){R:ℝ}{b:Bool}{r:ℝ}{k m n:ℕ}{a p:ℤ}{G:Gauge}
inductive Dog (q:ℕ+)(G:Gauge)(r:ℝ)(b:Bool):ℤ →Deck G→ Prop where
   | sky {p:ℤ}{f:Mist ℂ}: Chase q r p f → Dog q G r b p (Clove.glass f)
   | pet (f:Fan G)(k:ℕ): f∈ Reed.grads G k → Dog q G r b (k+1:ℕ) (Clove.fresh b f)
   | prod {a p:ℤ}{f g:Deck G}: Dog q G r b a f →Dog q G r b p g → Dog q G r b (a+p) (f*g)
   | plus {a:ℤ}{p s:Deck G}: Dog q G r b a p →Dog q G r b a s→ Dog q G r b a (p+s)
   | moves {a p:ℤ}{P:Deck G}:Dog q G r b a P→ p≤a → Dog q G r b p P
variable {f g:Mist ℂ} {P S: Deck G} {T:Submodule ℝ (Fan G)}
namespace Dog
lemma zero : Dog q G r b a 0:= by rw [show (0:Deck G)=glass 0 from funext fun i=> funext fun z=> (map_zero C).symm]; exact sky Chase.base
lemma one : Dog q G r b 0 1:= by rw [show (1:Deck G)=glass 1 from funext fun i=> funext fun z=> (map_one C).symm]; exact sky (Chase.quiet (1:ℂ))
lemma sc (c:ℂ)(h:Dog q G r b a P): Dog q G r b a (c • P):= by
    rw [show c • P=glass (Once (fun _=> c))*P from (glass₁ ..).symm]; rw [← zero_add a]; exact prod (sky (Chase.quiet c)) h
lemma fs {I:Type*}{p:I→Deck G}(l:Finset I)(h:∀ i∈l, Dog q G r b a (p i)) : Dog q G r b a (∑ i∈l,p i):= by induction l using Finset.induction_on with| empty=>rw [Finset.sum_empty];exact zero|insert i l h' ih=> rw [Finset.sum_insert h']; exact (h i (by simp)).plus (ih (fun j hj=> h j (by simp [hj])))
lemma bone (l:List (Bone G T)): Dog q G r b (feelB l) (floatP b (playB l)):= by
    induction l with
    | nil=> change Dog _ _ _ _ 0 (floatP b 1); rw [map_one]; exact one
    | cons c l IH=> unfold feelB playB; simp only [List.map_cons,List.prod_cons,List.sum_cons,Nat.cast_add]; rw [map_mul]; change Dog _ _ _ _ (↑(tipB c)+ feelB l) (floatP b (glyph _)* floatP b (playB l)); rw [float_glyph]; exact (pet _ _ c.order).prod IH
lemma trail {p:Curly G}(h:p∈ verse T n): Dog q G r b n (floatP b p):= by
    induction h using Submodule.span_induction with
    | mem p h=> obtain ⟨l,h,rfl⟩:=h; exact (bone l).moves (by exact_mod_cast h)
    | zero=> rw [map_zero]; exact zero
    | add a c _ _ y x=> rw [map_add];exact y.plus x
    | smul a c _ x=> rw [map_smul]; exact x.sc _
include hq
lemma poster {p:ℕ→Curly G}(h:p∈ Badge (Curly G) (Vanished q) (CakeH G)) (k:ℕ): Dog q G r false k (fun i _=>p i):= by
    induction h using Submodule.span_induction with
    | mem p h=>
       obtain ⟨f,b,h,hx,rfl⟩:=h; rw [show (fun (i:ℕ)(_ : Cover)=> f i • b)= glass (Once f)* floatP false b from ?_]; swap; · rw [glass₁,float_false]; rfl
       rw [← add_zero (k:ℤ)]; exact (sky (Chase.late_pay hq h k)).prod (trail hx)
    | zero=> exact zero
    | add a b _ _ x y=> exact x.plus y
    | smul a p h x=> exact x.sc _
lemma forever (P:Word G): Dog q G r false P.d (fun i _=> load q P i):= by
    let p : Deck G:= fun i _=> load q P i; let g: Deck G:=fun _ _=> Grow.looking P; change Dog _ _ _ _ _ p; exact (sub_add_cancel p g) ▸ (poster hq (self_ration hq P) P.d|>.plus (show Dog q G r false P.d g from by rw [show g=floatP false _ from (float_false _).symm]; exact trail (press_word P)))
end Dog
variable {A:ℕ→Brush G} (h:Tide q r A)
lemma exit_add (f g:Deck G) (A:ℕ→Brush G): exitP A (f+g)=exitP A f+exitP A g:= by ext1;ext1;simp [exitP]
@[simp] lemma exit_sky {A:ℕ→Brush G}: exitP A (glass f)=f:= by ext1;ext1;simp [exitP, glass,snap]
include hq h
lemma Dog.prism (hp:Dog q G r b a P): Chase q r a (exitP A P):= by
    induction hp with
    | sky h=> rw [exit_sky];exact h
    | pet p n hp=> unfold exitP Clove.fresh; simp_rw [carbon]; exact (Chase.root_pay hq h p hp b).com
    | prod p r hP hR=> rw [exit_mul];exact Chase.mulC hq hP hR
    | plus _ _ y t=> rw [exit_add];exact y.plus t
    | moves _ h t=> exact t.falls hq h
end YM.PositionX.Friend
