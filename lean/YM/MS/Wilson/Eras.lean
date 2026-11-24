import YM.MS.Book.LogCosts
import YM.MS.Book.ChargesM
import YM.MS.Wilson.Master
/-!
# The two bare reparametrization knobs (and ghost scale)

In Wilson LPT canonical plans. Affects all orders but leaves lower. Does not yet remove.
 Zero coefficient bookkeeping on identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Wilsonian
open Function Filter Set Finset Plane Koszul Cylinder Lab Book Convolve Program
open Paint Landau Bare Focus Taylor Draft Sew Chart Color Lattice Logarithm Orient
open PowerSeries (coeff)
variable {G:Gauge}{A P I:Type}(p:Team)(x:ℝ)

-- billing. field pairing uses density branch ghosts and spectral antifield inverse
def adap (a:Atom Axis): ℝ→Cn:= match a.1 with
   | some _=> if a.2 then opposite (fun i=> (p i).waveA) else affirmative (fun i=> (p i).waveA)
   | none=> if a.2 then opposite (fun i=>(p i).waveC) else affirmative (fun i=>(p i).waveC)
def fieldV (p:Team)(x:ℝ): Branch G Axis→Cn:= fun i=> adap p i.1 x
lemma adapR (a: Atom Axis): Ren (adap p a):= by
    unfold adap; split <;> split <;> first | exact Ren.inv (affirmativeRent _) | exact affirmativeRent _
lemma adap0 (a: Atom Axis): Low (adap p a x) := by rcases a with ⟨_|_,_|_⟩ <;> dsimp only [adap, Bool.false_eq_true, if_false,if_true] <;> first| exact o0 _ _| exact v0 _ _
lemma fieldV_l (i:ToneS G): fieldV p x ((Spectrum G).plain i) * fieldV p x ((Spectrum G).dual i)=1:= by
    rcases i with ⟨_,_⟩|i
    · exact pairs (fun i=> (p i).waveA) x
    exact pairs (fun i=> (p i).waveC) x
lemma price_mem (v:Dot G P): merit (fieldV p x∘ Prod.fst) 0 v.val=v.val:= by
    have hu (l:List (LightMode G P)): Low (l.map (fieldV p x∘ Prod.fst)).prod:= by
       induction l with| nil=>exact PowerSeries.coeff_zero_one| cons a l ih=>simp_rw [List.map_cons,List.prod_cons]; unfold Low; simp only [PowerSeries.coeff_mul,Finset.Nat.antidiagonal_zero,Finset.sum_singleton]; rw [ih,mul_one]; exact adap0 p x _
    funext l; rw [offer, hu, one_mul]
-- action and mark maps. marks have overall coupling reparam in input, compose with intrinsic polyn

def wobble (G:Gauge)(p:Team)(x:ℝ) : T (Dot G Cover)→ₗ[ℂ] T (Dot G Cover) := (car (fieldV p x∘Prod.fst)).comp (substitute (shift p x))
abbrev Actor (G:Gauge):= ℝ→ T (Dot G Cover)
def style (G:Gauge)(p:Team): Actor G:= fun x=> wobble G p x (core G)
lemma wob_mut {F:T (Dot G Cover)}(h:Mut (Spectrum G) F): Mut (Spectrum G) (wobble G p x F):= car_mut (fieldV p x) (Spectrum G) (fieldV_l p x) (subMut _ (share ..) h)
lemma wob_weight {F H:T (Dot G Cover)}(h:Weightless (Spectrum G) F H): Weightless (Spectrum G) (wobble G p x F) (wobble G p x H):= car_Weight (fieldV p x) (Spectrum G) (fieldV_l p x) (subWeight _ (share ..) h)
lemma main_law (G:Gauge)(p:Team)(x:ℝ)(h:G.Simple): Mut (Spectrum G) (style G p x):= wob_mut p x (coreQ G h)
lemma whoZero (F:T (Dot G Cover)): wobble G p x F 0= F 0 := by unfold wobble; rw [LinearMap.comp_apply,rolls,Finset.Nat.antidiagonal_zero,Finset.sum_singleton,pay0]; apply Subtype.ext; rw [train_v]; exact price_mem ..
lemma sets_origin (G:Gauge)(p:Team)(x:ℝ): style G p x 0=levels 2 (W G) 0:= by rw [style,whoZero,at_rest]
lemma wob_steady {F S:T (Dot G Cover)}: steadyE (Spectrum G) (wobble G p x F) (wobble G p x S) = wobble G p x (steadyE (Spectrum G) F S):=by
   show steadyE (Spectrum G) (dotD (fieldV p x) _) (dotD (fieldV p x) _)= dotD (fieldV p x) _; rw [car_steady _ (Spectrum G) (fieldV_l p x), modSub (Spectrum G) (share ..)]
-- bound & shape; ready.
variable {h:ℤ}
local notation "V"=> fieldV p x
-- count form
lemma wob_trained (v:Dot G P)(hQ:Tuned v h)(i:ℕ): Tuned (train (V∘ Prod.fst) i v) h:= by
    have he (l:List (LightMode G P)) : Decent (fun x:ℝ=> coeff i (l.map ((fieldV p x) ∘ Prod.fst)).prod):= Ren.swath (fun k:LightMode G P=> adap p k.1.1) (fun k=>adapR p _) _ i -- placeholder
    have hs := hQ.symm; have hw:=hQ.ghost; have hl:=hQ.still
    refine ⟨fun l i j r=>?_,fun l h=>?_,fun l=>?_⟩ <;> simp_rw [train_v,offer]
    · rw [hs l i j r]; simp only [List.map_append,List.map_cons,List.prod_append,List.prod_cons]; rw [mul_left_comm ((V∘Prod.fst) i)]; exact mul_left_comm .. -- ] -- inspect
    · rw [hw l h,mul_zero]
    rw [star_mul',hl,he _ |>.starv x] -- syntax
lemma dye_train (v:Dot G P) (k:ℕ)(f:G.El): dye f (train (V ∘ Prod.fst) k v)=train (V∘Prod.fst) k (dye f v):= by
    refine Subtype.ext (Eq.symm (pennantC (coeff k) v (V ∘ Prod.fst) (V ∘ Prod.fst) (tintC (stripe G _) f) (fun i j h=> ?_))); -- leg compare
    change adap p j.1.1 x=adap p i.1.1 x; rw [show j.1.1=i.1.1 from Classical.byContradiction (fun ht=> h (offC _ _ _ _ (fun hh=> ht (congr_arg (fun i:(Atom Axis×P)=>i.1) hh).symm)))]
lemma stanceTrain (v:Dot G Cover)(i:ℕ)(h: stance v): stance (train (V ∘ Prod.fst) i v):= by
   have hu (k:Signed)(F:Dot G Cover) : pose k (train (V∘Prod.fst) i F)=train (V ∘Prod.fst) i (pose k F):= by
       have hb (k:Signed)(j:LightMode G Cover) : V (turn k j).1=V j.1:= by rcases j with ⟨⟨⟨_|j,t⟩,u⟩,x⟩ <;> rfl
       have hc : graffiti (σ k) (train (V∘Prod.fst) i F)=train (V∘Prod.fst) i (graffiti (σ k) F):= Subtype.ext (funext fun _=>mul_left_comm ..)
       unfold pose; rw [LinearMap.comp_apply,hc]; exact pennant_ferry (turn k) (coeff i) (V∘Prod.fst) (V∘Prod.fst) (fun t=> (hb k t).symm) _
   exact fun k=> (h k).mono fun n ht=> by rw [hu]; change duty true n _=duty true n _; rw [mission,mission]; exact congr_arg _ ht
end YM.MS.Native.Wilsonian
