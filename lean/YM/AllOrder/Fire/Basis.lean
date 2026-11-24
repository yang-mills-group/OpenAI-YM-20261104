import YM.AllOrder.Fire.Factors
import YM.AllOrder.Fire.Length
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Finset Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory Response
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "Ω"=>X×Y
local notation "T" => ℝ×(X×Y)
open GaussianScore
inductive Stack (X Y:Type) [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y] (n:ℕ): ((X×Y)→ℝ)→Prop where
   | base {t:X→ℝ}{s:Y→ℝ}: Rank X n t → Plausible s → Stack X Y n (fun p=> t p.1*s p.2)
   | adds {f g:(X×Y)→ℝ} : Stack X Y n f→Stack X Y n g→Stack X Y n (f+g)
variable {f g:X×Y→ℝ} {n m:ℕ}
namespace Stack
lemma plain (h:Stack X Y n f): Plausible f:= by induction h with
   | base h H=> exact (h.read.app (LinearMap.fst ℝ X Y)).mul (H.app (LinearMap.snd ℝ X Y))
   | adds _ _ i j=>exact i.add j
lemma mult (h:Stack X Y n f)(hh:Stack X Y m g): Stack X Y (n+m) (f*g):= by
 induction h with
 | @base t u h hu=>
    induction hh with
    | @base v r hv hr=> convert Stack.base (h.mul hv) (hu.mul hr) using 1; ext p; simp only [Pi.mul_apply]; ring
    | adds he hf i j=> rw [mul_add]; exact i.adds j
 | adds he h i j=> rw [add_mul]; exact i.adds j
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
 [MeasurableSpace Y][BorelSpace Y]
lemma overall (h:Stack X Y n f)(Γ:Law Y)(μ:Measure Y)[μ.IsAddHaarMeasure]: Rank X n (bound Γ μ f) := by
 induction h with
 | base hf hh => rw [core_bound]; exact hf.scal _
 | adds hf hh i j=> rw [bound_add Γ μ hf.plain hh.plain]; exact i.add j
end Stack
section fire

def wardrobe (p:(ℝ×(X×Y))×Y): Ω:= (p.1.2.1, p.1.2.2+p.1.1• p.2)
def blow (f:Ω→ℝ) := f ∘ wardrobe
lemma tarried (h:Rank Ω n f) : Stack (ℝ × Ω) Y n (blow f):= by
 induction h with
 | nil i c=> exact (show (fun (_:T×Y)=> c*1)=blow (fun _=> c) by simp [blow,Function.comp_def]) ▸ Stack.base (Rank.nil i c) (Plausible.atom (1:ℝ))
 | @dot L n f h ih=>
    let V:=L∘L ContinuousLinearMap.inr ℝ X Y
    let D:=ContinuousLinearMap.fst ℝ ℝ Ω
    let E:=L ∘L ContinuousLinearMap.snd ℝ ℝ Ω
    let r (p:T×Y):= E p.1*1+D p.1*V p.2; have hr : Stack T Y 1 r:= (Stack.base (Rank.line E) (Plausible.atom (1:ℝ))).adds (Stack.base (Rank.line D) (Rank.line V).read)
    have h : blow ((L: Ω→ℝ)*f)=blow f*r := by
     funext x; simp only [blow,r,Function.comp_apply, Pi.mul_apply]; rw [show wardrobe x=x.1.2+(x.1.1• ((0:X),x.2)) from ?_,map_add,map_smul] -- affects f on rhs? same
     · change (((E x.1)+D x.1*V x.2)*_)= _*(E x.1*1+D x.1*V x.2); rw [mul_one, mul_comm]
     obtain ⟨⟨t,u,v⟩,y⟩:=x; simp [wardrobe]
    exact h.symm ▸ ih.mult hr
 | add h H i j=>exact i.adds j
lemma blown {f:X×Y→ℝ} (h:Plausible f) [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]: Plausible (blow f):= by
 obtain ⟨n,hn⟩:(∃ n,Rank Ω n f):=by
    induction h with
    | atom c=> exact ⟨0, Rank.nil _ _⟩
    | times f L h H=> obtain ⟨n,hn⟩:=H; exact ⟨n+1,hn.mul (Rank.line L.toContinuousLinearMap)⟩
    | add h h' H H'=> obtain ⟨n,hn⟩:=H; obtain ⟨m,hm⟩:=H'; exact ⟨max n m, (hn.up (le_max_left ..)).add (hm.up (le_max_right ..))⟩
 exact (tarried hn).plain
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
 [MeasurableSpace Y][BorelSpace Y]
def Hot (Γ:Law Y)(μ:Measure Y)(f:X×Y→ℝ): T→ℝ := bound Γ μ (blow f)
lemma savor (h:Rank Ω n f)(Γ:Law Y)(μ : Measure Y)[μ.IsAddHaarMeasure]: Rank T n (Hot Γ μ f):= (tarried h).overall ..
lemma flavor (h:Plausible f)(Γ:Law Y)(μ:Measure Y)[μ.IsAddHaarMeasure]: Plausible (Hot Γ μ f):= smooth_bind Γ μ (blown h)
end fire
end YM.AllOrder.Fire
