import YM.RG11Proof.Fields.Winding
import YM.RG11Proof.Arrow.Chain
import YM.Next.MAXWELL.System

/-!
# Conversion of derivative labels

Keep derivative motion (E_h to E_h+1) at *each scheme*, integrating
HEAD position derivative in conf weak form (minus sign, no contacts).
From converted two-point coefficients at these fixed & derivative profiles
with all other slots, and tested MS and X derivative identities through N,
PROVE that it commutes through N with field & coupling changes. Field
systems may use exact E lifts only for this separated assertion (and need
prove those identities also on inserted Wilson operators, including capture
and mesh removal). For multi derivatives iterate with growing announced
powers and horizons; not valid as-is at contacts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Arrow
open scoped ContDiff BigOperators Classical
open YM.RG11.Fields YM.RG11.Jets YM.RG11.Nodes PowerSeries Labels Maxwell
open Analysis
variable {G:Gauge}{F:Frames G}(A:ShapeReport G F){d n:ℕ}(B:Basis F d)

def question (f:Test n):reading B.J (PowerSeries ℝ) n:=fun z=>A.realAt B (⟨⟨n,f⟩,z⟩)

 theorem plant_question (p:Change ℝ B.J)(f:Test n)(z:Fin n→B.J):
   p.act (A.realAt B) (⟨⟨n,f⟩,z⟩) = plant p.Z (PowerSeries.subst p.g ∘question A B f) z:=rfl

/-- Minus position derivative on the profile. -/
def plans {n}(a:Axis)(i:Fin n): Test n→L[ℂ] Test n:= -TestFunction.lineDerivCLM ℂ (Points.direction i a)
 theorem plans_at (a:Axis)(i:Fin n)(f:Test n)(x:Points n): plans a i f x=-Points.gradient i a f x:=by
   change -(TestFunction.lineDerivCLM (k:=⊤) ℂ _ f x)=_
   rw [TestFunction.lineDerivCLM_eq_fderivCLM (k:=⊤),show (TestFunction.fderivCLM ℂ ⊤ ⊤ f:Points n→ Points n →L[ℝ] ℂ)=_ from TestFunction.fderivCLM_apply_of_le f le_top]; rfl

abbrev lane {d:ℕ}(B:Basis F d)(C:Basis F (d+1)):= Axis→Rect B.J C.J (PowerSeries ℝ)

variable (C:Basis F (d+1))(ι:B.J↪ C.J)

/-- Representative-independent weak translations on the displayed
2 slot inputs through N. Provide separately for Wilson & MS, all profiles.
Incoming fields at d and spectator may range to d+1. `arrive_all`
for arbitrary responses is stronger. (`A.realAt` uses re only and real
frames; can rotate f by phase for im data). -/
def Arrives (X:lane B C)(N:ℕ):Prop:=
    ∀ (a:Axis)(t:Test 2)(w:Fin 1→C.J)(i:B.J), Through N (armed (X a i) (question A C t) w)
          (question A C (plans a 0 t) (Fin.cons (ι i) w))

-- leading two-slot coercivity for derivative mismatch (don't require b∈V)
 theorem reliable (u:B.J→ℝ) (h:∀ (f:Test 2) (w:Fin 1→B.J), armed u (fun v=>constantCoeff (question A B f v)) w=0): u=0:=by
   obtain ⟨f,hf⟩:=positive_profile B (Free.hierarchy F) (0:Axis)
   by_contra hu
   have he(i) : (∑ j,u j*(freePair B f) j i)=0:=by
      have hv:=h f (fun _=>i)
      unfold question at hv; simp_rw [A.price0] at hv
      have ht (j):rowZero B (⟨⟨2,f⟩,Fin.cons (α:=fun _:Fin 2=>B.J) j (fun _ : Fin 1=>i)⟩:point B)=freePair B f j i:=by
        change (Pert.Position.wickReading F d f _).re=(Pert.Position.wickReading F d f _).re
        apply congrArg Complex.re; apply congrArg _; ext1 t; fin_cases t <;> rfl
      unfold armed at hv; simp_rw [ht] at hv; exact hv
   have hP := hf u hu
   unfold Bridge.gramAt at hP
   have hZ(i:B.J): (∑ i',u i' * ∑ l, frameMirror B 0 i l * freePair B f i' l)=0:=by
       simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; simp_rw [mul_left_comm (u _),←Finset.mul_sum,he,mul_zero,Finset.sum_const_zero]
   simp [hZ] at hP

 theorem intertwine (Z:ShapeReport G F)(p:Change ℝ C.J)(hZ:Horizon.Held ι p.Z)(hg:Anchored p.g)(hd:nearId p.Z){N}
    (h:∀ v,Through N (p.act (A.realAt C) v) (Z.realAt C v)){X Y:lane B C}(hx:Arrives A B C ι X N)(hy:Arrives Z B C ι Y N)(a:Axis):
    MatThrough N (Y a*p.Z) (Horizon.take ι p.Z*subs p.g (X a)):=by
   let D:=Y a * p.Z-Horizon.take ι p.Z*subs p.g (X a)
   have H (f:Test 2)(i:B.J)(v:Fin 1→C.J): Through N (plant p.Z (armed (D i) (PowerSeries.subst p.g ∘ question A C f)) v) 0:=
      zeroes p hg hZ (fun i w=>hx a f w i) (fun i w=>hy a f w i) (fun w=> by rw [←plant_question]; exact h _) (fun w=>by rw [←plant_question]; exact h _) i v
   apply MatThrough.of_piece
   have HZ(k)(hk:k≤N): piece k D=0:=by
      induction k using Nat.strong_induction_on with
      | h k ih=>
        apply Matrix.ext; intro i j
        apply congrFun (reliable A C (piece k D i) (fun f w=>?_)) j
        have hv:= H f i w k hk
        rw [invader p.Z (by convert! hd) (PowerSeries.subst p.g ∘ question A C f),map_zero] at hv
        simp_rw [Function.comp_apply,base_compose _ _ hg] at hv; exact hv
        exact fun i hi=>ih i hi (hi.le.trans hk)
   intro k hk; have he:=HZ k hk; apply sub_eq_zero.mp; rw [←he]; ext z v; simp [D]
end YM.RG11.Arrow
