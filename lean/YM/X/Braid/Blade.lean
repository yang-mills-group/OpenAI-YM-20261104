import YM.X.Braid.Weir
/-!
# Exact alias K⁻¹ proof. Works on ALL Shelf even non-invariant matrices and for arbitrary supports.
Forward differences act on positive form; over the cover subtract zero constant as gradient too!
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Braid
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter MeasureTheory Metric Finsupp
open Stems Reed Interval Hinge CellsInt
open Stems (Brush) -- duplicate
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}
local notation "R"=> Hair G →₀ ℝ
local notation "H"=> Hair G
variable (n:Side)(f g:Fan G) (z t:Cover)(i j:Axis)(y:Hair G)
def ignored (n:Side):ℝ := ((n.val):ℝ)^(-4:ℤ)
lemma deposit_cane : ∑ i:Axis, rewind (stepValue (fun z=>cane n z t) i) i z= -(if wrap n z= wrap n t then 1 else 0)+ ignored n:= by
     let x:=wrap n z-wrap n t; let L:= (green (n:=n)); have he : ∑ i:Axis, rewind (stepValue (fun z=>cane n z t) i) i z= Pert.Orb.lap L x := by
        refine Finset.sum_congr rfl fun i _=>?_ ; simp only [rewind,stepValue,cane,sub_add_cancel,map_sub,map_add,wrap_step]; rw [show (wrap n z+step i)-(wrap n t)=x+step i by unfold x; abel, show wrap n z-step i- wrap n t=x-step i by unfold x; abel]; unfold L x; abel
     rw [he]; change Pert.Orb.lap (fun p=> (Pert.Full.toroid (n:=n) p).re) x= _
     rw [Pert.Orb.lap_shift]; simp [x,ignored,sub_eq_zero]

private lemma paint_at (b a:Axis)(x:Cover) (k l:G.ColorIndex): (raising b (paints n (Finsupp.single ((t,a),k) 1))) x l = if l=k ∧ b=a then cane n x t else 0:= by change text (paints n (Finsupp.single _ 1)) ((x,b),l)=_; rw [text_paints, linearCombination_single,one_smul]; rfl
lemma cane_left : rewind (fun x=>cane n x t) i z= -(stepValue (fun b=>cane n z b) i t):= by
   unfold rewind stepValue cane; simp only [map_sub,map_add,wrap_step, sub_add_cancel]; rw [show wrap n z-(wrap n t+step i)=wrap n z-step i-wrap n t by abel]; ring
lemma cross (b:Axis) (i j:Axis) (k l:G.ColorIndex):
     let v:= paints n (Finsupp.single ((t,b),l) 1);
     rewind (stepValue (raising i v) j) i z k= if k=l∧i=b then -(stepValue (fun t=>stepValue (fun z=>cane n z t) j z) b t) else 0:= by
     intro v
     unfold rewind stepValue; simp only [PiLp.sub_apply,v,paint_at]; split
     next h=> simp only [*,↓reduceIte]; have h₁:= cane_left n (z+step j) t b; have h₂:=cane_left n z t b; simp only [rewind,stepValue,sub_add_cancel] at h₁ h₂; rw [sub_add_cancel,show z-step b+step j= z+step j-step b by abel]; linarith
     next h=> simp [h]
lemma alias_calculated (k l:G.ColorIndex): orderK j (paints n (Finsupp.single ((t,i),l) 1)) z k =
  (if wrap n z=wrap n t ∧ j=i ∧ k=l then 1 else 0) - (if k=l ∧ j=i then ignored n else 0) - if k=l then stepValue (fun b=>stepValue (fun x=>cane n x b) j z) i t else 0:= by
    let b:=((t,i),l); let A:= paints n (Finsupp.single b 1);
    rw [key_split]; have he (X:Axis→ G.Color): (∑ i,X i) k= ∑ i:Axis,X i k:= map_sum (EuclideanSpace.proj k:G.Color→L[ℝ] ℝ) X Finset.univ
    have hv (x:Axis): stepValue (rewind (raising x A) x) j z = rewind (stepValue (raising x A) j) x z:= by unfold rewind; simp only [stepValue,sub_add_cancel]; rw [show z-step x+step j=z+step j-step x by abel]; abel -- check second order signs
    have hy (x:Axis): rewind (stepValue (raising j A) x) x z k = if k=l∧ j=i then rewind (stepValue (fun x=>cane n x t) x) x z else 0:= by
       simp only [rewind,stepValue,PiLp.sub_apply, A,b,paint_at];split_ifs<;> simp
    change (-(∑ x:Axis, rewind (stepValue (raising j A) x) x z)+(∑ x:Axis,stepValue (rewind (raising x A) x) j z)) k=_
    simp_rw [PiLp.add_apply,PiLp.neg_apply,he,hv, hy, show ∀ a:Axis, rewind (stepValue (raising a A) j) a z k=_ from fun a=> cross n z t i a j k l]; by_cases h:k=l; swap; · simp [h]
    simp only [h,true_and, ↓reduceIte,and_true]; rw [Finset.sum_ite_irrel, Finset.sum_ite_eq']; split_ifs <;> simp_all [deposit_cane] <;> abel -- orientation error parameters

def twin (n:Side)(x:Hair G): Brush G:= textL.symm (fun y=> if place (0:Site n) y=place 0 x then 1 else 0)
def anomaly (n:Side)(x:Hair G)(t:Cover) : G.Color:= WithLp.toLp 2 (fun k=> if k=x.2 then (ignored n * (t x.1.2)+ stepValue (fun z=>cane n z t) x.1.2 x.1.1) else 0)
lemma pays : paints n (keyRow y)=twin n y - raised (anomaly n y):= by
    funext p; apply PiLp.ext; intro k; change text (paints n (keyRow y)) (p,k)=_
    rw [← flat₁,commute,reading]; let i:=y.1.2; let z:= y.1.1; let x:=p.1; let j:=p.2
    rw [← show orderK i (paints n (Finsupp.single ((p.1,p.2),k) 1)) z y.2= _ from rfl,alias_calculated];
    change _=(if place (0:Site n) (p,k)=place 0 y then 1 else 0)- (anomaly n y (x+step j) k-anomaly n y x k); simp only [place,west,Prod.mk.injEq,add_zero,anomaly,PiLp.toLp_apply,Pi.add_apply];
    unfold i j z x; simp only [step_apply]
    conv => lhs; simp only [eq_comm (a:=y.2) (b:=k), eq_comm (a:=y.1.2) (b:=p.2), eq_comm (a:=wrap n y.1.1) (b:=wrap n p.1)]
    by_cases hp:k=y.2 <;> by_cases hx:p.2=y.1.2 <;> by_cases hq:wrap n p.1=wrap n y.1.1 <;> simp_all [stepValue,eq_comm] <;> ring
lemma horizontal_pays (x:Hair G)(h:f∈ Reed.Horizontal G) : orderK x.1.2 (paints n f) x.1.1 x.2 = flatL (twin n x) f:= by
    rw [← reading,commute,pays,← taste_eval,map_sub, horn h,sub_zero,taste_eval]
end YM.PositionX.Braid
