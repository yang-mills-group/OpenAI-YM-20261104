import YM.Contacts.Procession.Rudder
/-!
# Physical marked rank recursion

Periods first. Marker Leg timing uses its own finite horizon. Shift comparison quantitative,
does not discard disconnected from relative observer samples.A later marker reset uses these explicit coefficients.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Procession.Sun
open Function Set Filter Pulse Matrix MeasureTheory Finset
open Milling Milling.Forge Pulse.Form
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {α Y: Type} [Fintype α] (g:α→α→ℝ) {i p k t l r e :ℕ}{A V:House α} (h:Snug A)
structure Proper (n:ℕ)(V:House α):Prop where
   sym i j: Poem (V i j)
   thin (i j:ℕ): n+i < j → V i j=0
lemma plot (X Z:GridTime α)(i j n:ℕ):convK g X Z i j n= ∑ u∈antidiagonal i,∑ t∈antidiagonal j,∑ r∈antidiagonal n, light g n r.1 r.2 (X t.1 u.1) (Z t.2 u.2):= by unfold convK; simp_rw [Finset.sum_apply]; rfl
include h
lemma tone (Y:House α)(hv:Proper p Y)(t:ℕ): Proper p (walk g A Y t):= by
   induction t using Nat.strongRecOn with| _ t ih =>
   cases t; · rwa [walk_start]
   rename_i t; let H:= gathering g A; let X:= walk g A Y; let u:= ((((t+1:ℕ):ℝ))⁻¹ )
   have hk(v w:ℕ)(P Q:St α)(n:ℕ) : Poem (light g n v w P Q):= by
      unfold light; split
      next he=> subst n; exact Poem.scale (print_even _) _
      exact Poem.empty
   constructor
   · intro i j; simp_rw [walk_step, Pi.smul_apply, indus,Pi.add_apply,plot]; refine Poem.scale (Poem.add (Poem.add ?_ ?_) ?_) _
     · exact (print_even _).scale _
     · exact Poem.sum _ fun _ _=> Poem.sum _ fun _ _=> Poem.sum _ fun _ _=> hk _ _ _ _ _
     exact Poem.sum _ fun _ _=> Poem.sum _ fun _ _=> Poem.sum _ fun _ _=> hk _ _ _ _ _
   intro i j hj
   have hx : convK g H X i t j=0 := by
      rw [plot]; apply Finset.sum_eq_zero; intro a ha; apply Finset.sum_eq_zero; intro b hb; apply Finset.sum_eq_zero; intro v hu; have ht:=mem_antidiagonal.mp hu; have hz:=mem_antidiagonal.mp hb; have ha:=mem_antidiagonal.mp ha; by_cases hl:a.1=0 ∨ a.1+2<v.1+1; · exact light_close_left g ((h.bounded g b.1).thin _ _ hl)
      exact light_close_right g ((ih b.2 (by omega)).thin _ _ (by omega))
   have hy : convK g X H i t j=0 := by
      rw [plot]; apply Finset.sum_eq_zero; intro a ha; apply Finset.sum_eq_zero; intro b hb; apply Finset.sum_eq_zero; intro v hu; have ht:=mem_antidiagonal.mp hu; have hz:=mem_antidiagonal.mp hb; have ha:=mem_antidiagonal.mp ha; by_cases hl:a.2=0 ∨ a.2+2<v.2+1; · exact light_close_right g ((h.bounded g b.2).thin _ _ hl)
      exact light_close_left g ((ih b.1 (by omega)).thin _ _ (by omega))

   rw [walk_step]; change u • (Pulse.degree g (X t i (j+2)) + convK g H X i t j+convK g X H i t j)=0; rw [hx,hy, show X _ _ _=0 from (ih t (by omega)).thin _ _ (by omega),Pulse.nova]; simp
include h
lemma bounds_t (Y:House α)(hv:Proper p Y) (x:ℕ)(hp:p+3*e<r+2*x): walk g A Y x e r=0:= by induction x using Nat.strongRecOn generalizing e r with| _ x ih=>
   cases x; · rw [walk_start]; exact hv.thin _ _ (by omega)
   rename_i t; let i:= e; let j:=r; let H:= gathering g A; let X:= walk g A Y; let u:= ((((t+1:ℕ):ℝ))⁻¹ )

   have hx : convK g H X i t j=0 := by
      rw [plot]; apply Finset.sum_eq_zero; intro a ha; apply Finset.sum_eq_zero; intro b hb; apply Finset.sum_eq_zero; intro v hu; have ht:=mem_antidiagonal.mp hu; have hz:=mem_antidiagonal.mp hb; have ha:=mem_antidiagonal.mp ha; by_cases hl:3*a.1<v.1+1+2*b.1; · exact light_close_left g (h.timed g b.1 _ _ hl)
      exact light_close_right g (ih b.2 (by omega) (by omega))

   have hy : convK g X H i t j=0 := by
      rw [plot]; apply Finset.sum_eq_zero; intro a ha; apply Finset.sum_eq_zero; intro b hb; apply Finset.sum_eq_zero; intro v hu; have ht:=mem_antidiagonal.mp hu; have hz:=mem_antidiagonal.mp hb; have ha:=mem_antidiagonal.mp ha; by_cases hl:3*a.2<v.2+1+2*b.2; · exact light_close_right g (h.timed g b.2 _ _ hl)
      exact light_close_left g (ih b.1 (by omega) (by omega))

   rw [walk_step]; change u • (Pulse.degree g (X t i (j+2)) + convK g H X i t j+convK g X H i t j)=0; rw [hx,hy, show X _ _ _=0 from ih t (by omega) (by omega),Pulse.nova]; simp
omit h
lemma strange (A V Y:GridTime α)(z:ℝ): indus g A (z • V + Y) i t = z • indus g A V i t + indus g A Y i t := by -- t not var
   unfold indus; simp [convK,smul_add,sum_add_distrib,smul_sum]; abel
lemma process_linear (A Y V:House α)(s:ℝ): walk g A (s • Y+ V) i=s • walk g A Y i+walk g A V i:= by
   induction i using Nat.strongRecOn with|_ i ih=>
    cases i; simp_rw [walk_start]
    rename_i i; ext1 e; let P:=walk g A; let Z:= gathering g A; have he(j): indus g Z (P (s • Y+V)) j i=indus g Z (s • P Y+P V) j i:= respects g _ _ _ (fun j hj=> ih j (by omega)); change _=s • walk g A Y (i+1) e + walk g A V (i+1) e; rw [walk_step,walk_step,walk_step,he,strange,smul_add,smul_comm s]

def canal (g:α→α→ℝ) (p:ℕ)(A V: House α): House α:= fun i=> ∑ j∈Finset.range (p+3*i+1),walk g A V j i
include h
lemma marsh (hf:Proper p V): Proper p (canal g p A V):= by
   refine ⟨fun i j=>?_,fun i j he=>?_⟩; · simp_rw [canal,Finset.sum_apply]; exact Poem.sum _ fun k _=> (tone g h V hf k).sym _ _ -- too many args
   simp_rw [canal,Finset.sum_apply]; exact sum_eq_zero fun k _=> (tone g h V hf k).thin i j he
lemma bracket (Y:House α)(hv:Proper p V)(he:e< 2*i)(hk:p ≤ 3*i)(hy:∀ j≤ e, Y j=A j + shiftA i V j) : massaged g Y e= massaged g A e+shiftA i (canal g p A V) e := by
   ext1 j; rw [Pi.add_apply, massaged,massaged]; have hp l := statute (j:=l) g A V (show e < i+i from by omega) hy; simp_rw [hp,Pi.add_apply, sum_add_distrib]; apply congr_arg; unfold paceA shiftA; split; next hU=> rw [canal, Finset.sum_apply]; exact (sum_subset (Finset.range_mono (by omega)) (fun l hl ht=> bounds_t g h V hv l (by rw [Finset.mem_range] at ht; omega))).symm
   simp
omit h
lemma canal_linear (V Y:House α)(s:ℝ): canal g p A (s • V+ Y)=s • canal g p A V+canal g p A Y:= by funext i; simp_rw [canal, process_linear g A V Y s,Pi.add_apply,Pi.smul_apply, Finset.sum_add_distrib]; simp [canal,smul_sum]
include h
lemma pure_row (V:House α)(hv:Proper p V): canal g p A V 0 p= V 0 p:= by unfold canal; rw [Finset.sum_apply,sum_eq_single 0]; rw [walk_start]; intro b _ hh; exact bounds_t g h V hv b (by omega); simp
end YM.Contacts.Procession.Sun
