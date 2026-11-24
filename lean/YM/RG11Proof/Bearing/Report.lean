import YM.RG11Proof.Bearing.Tone
import YM.RG11Proof.Travel.Evolve
/-!
# CS conversion in final frame from the constructed mass-independent recipe

WilsonX continuum prescriptions may first supply the pre-adjustment
position frame (filtration-lowering N repinning still needed); same
prescription derivative & β self transport. Need prove THIS recipe matches
the promised one. This is an algebraic application to the tested arrays
already equipped with independent preadjustment CS. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bearing
open PowerSeries YM.RG11.Jets YM.RG11.Scale YM.PertExtension.Position
open scoped BigOperators Classical
variable {J P I:Type*}[Fintype J]{width:P→ℕ}(w:J→ℕ)(E:Keeper width)
local notation "ps"=> PowerSeries ℝ

-- Engineering shift as frame orbit with d*C.
private theorem asorbit (A:ArrayAt J ℝ width)(v:Mark J width): C (bulk w v)*A v=orbit A v (diagonalX w):=by
  unfold orbit bulk; rw [map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  classical
  rw [Finset.sum_eq_single_of_mem (v.2 i) (Finset.mem_univ _) (fun j _ hj=>?_)]
  · simp only [diagonalX, Matrix.map_apply,arch, Matrix.diagonal_apply_eq,Function.update_eq_self]
  simp only [diagonalX, Matrix.map_apply,arch,Matrix.diagonal_apply_ne _ hj.symm,map_zero,zero_mul]

private theorem varies_thru {k}{A B:Square J ps}(h:MatThrough k A B)(q:ArrayAt J ℝ width)(Z:Square J ps)(v):
    Through k (varies q Z A v) (varies q Z B v):=Through.sum fun _ _=> (Through.refl _).mul (Through.sum fun _ _=> (h _ _).mul (Through.refl _))

local notation "slots"=>PertExtension.Position.insert

-- precise finite transformation, Euler in same sign
 theorem revises (A:ArrayAt J ℝ width){k}{N b l:Square J ps}{β:ps}(h:Stem k E w A β b)(H:MatThrough k (l*N) (rephase w β b N)):
    Stem k E w (slots J width A (fun i j=>N i j)) β l:=by
   let V:=slots J width A (fun i j=>N i j)
   let p:Change ℝ J:=⟨PowerSeries.X,N⟩
   have ht(A:ArrayAt J ℝ width):p.act A=slots J width A (fun i j=>N i j):=by unfold Change.act p; simp [X_subst]
   let d:=diagonalX w
   have hd':Anchored p.g:=Anchored.variableX
   intro v
   let Δ:=β • flash N-l*N+N*b
   have hw : Through k (slots J width (euler E w A) (fun i j=>N i j) v) (p.act (call β b A) v):= by rw [ht]; exact Through.slots (fun i=>h _) (fun i j=> Through.refl _)
   have hx : call β l (p.act A) v- p.act (call β b A) v = varies A N Δ v:=by
      rw [next_left p A β β l b hd',leftover,show p.g=PowerSeries.X from rfl]
      simp only [derivative_X,X_subst,mul_one,sub_self,zero_mul,PertExtension.Position.insert,Finset.sum_const_zero,zero_add,subs_X]; rfl
   have hp(v) : orbit (slots J width A (fun i j=>N i j)) v d=varies A N (d*N) v:=by rw [←varies_orbit,varies_exterior,one_mul]
   have hi : euler E w V v = slots J width (euler E w A) (fun i j=>N i j) v + varies A N (N*d-d*N) v:=by
      simp_rw [euler, asorbit]; unfold V; rw [Keeper.move_slot,hp,← responds_at A N (N*d-d*N), map_sub]
      rw [show euler E w A=A ∘ E.move-(fun z=>orbit A z d) from funext fun i=>by rw [euler,asorbit]; rfl]
      change slams N v (A ∘ E.move)-varies A N (d*N) v = slams N v (A ∘ E.move - (fun z=>orbit A z d))+_
      rw [map_sub,responds_at,responds_at, show (fun z=>orbit A z d) = varies A 1 d from funext fun z=> (varies_orbit ..).symm,
          slams_at (varies A 1 d) N v, varies_interior, mul_one]; abel
   rw [hi]
   rw [sub_eq_iff_eq_add,add_comm,ht A] at hx
   rw [hx]
   apply hw.add
   apply varies_thru
   -- precise compensation.
   have hN : MatThrough k Δ (N*d-d*N):= fun i j=>by
      convert! (((Through.refl ((β • flash N) i j)).sub (H i j)).add (Through.refl ((N*b) i j))) using 1
      simp only [rephase, Matrix.add_apply, Matrix.sub_apply, d]
      abel
   exact hN.symm
end YM.RG11.Bearing
