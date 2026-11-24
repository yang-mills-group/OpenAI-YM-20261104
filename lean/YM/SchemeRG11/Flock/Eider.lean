import YM.SchemeRG11.Flock.Pascal
/-!
Exact cover Hodge at the top homogeneous symbol, including harmonic lifts.
No torus zero-mode assertions. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Flock
open Function Lattice
variable {E F:Type*} [AddCommGroup E][AddCommGroup F][Module ℝ E][Module ℝ F]
-- minus the kinetic operator
abbrev rear (i:Axis):Module.End ℝ (Plane E):=hop (-step i)*soar i
lemma rear_apply (i:Axis)(f:Plane E)(x:Cover):rear i f x=f x-f (x-step i):=by
 change soar i f (x+-step i)=_; rw [soar_apply,←sub_eq_add_neg,sub_add_cancel]
lemma soar_rear (i j:Axis)(f:Plane E): soar i (rear j f)=rear j (soar i f):=by
 funext x; rw [soar_apply,rear_apply,rear_apply,rear_apply,soar_apply,soar_apply]; rw [add_sub_right_comm]; abel
lemma rear_low (m:ℕ)(f:Plane E)(h:f∈cap E (m+1))(i:Axis): rear i f∈cap E m:= hop_cap (soar_lower m f h i) _
def lap:Module.End ℝ (Plane E):=∑ i:Axis,rear i*soar i
lemma lap_lower {m:ℕ}{f:Plane E}(h:f∈cap E (m+2)): lap f∈cap E m:=by rw [lap,LinearMap.sum_apply]; exact Submodule.sum_mem _ fun i _=> rear_low _ (soar i f) (soar_lower _ _ h i) _
lemma tip (m:ℕ)(f:Plane E)(h:f∈cap E (m+2))(t:Fliers)(ht:t.card=m)(i:Axis)(x y:Cover): fleet t (rear i f) x=fleet (i ::ₘ t) f y:=by
 change fleet (E:=E) t (hop (-step i) (soar i f)) _= _; rw [jump]; refine Eq.trans ?_ (landed (member.mp h) _ (by simp [ht]) (x+-step i) y); rw [fleet_cons']; rfl
lemma lap_top (n:ℕ)(f:Plane E)(h:f∈cap E (n+3))(s:Fliers)(hs:s.card=n)(x y:Cover): fleet s (lap f) x = ∑ i:Axis, fleet (i ::ₘ i ::ₘ s) f y:=by
 rw [lap,LinearMap.sum_apply,map_sum,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i hi
 change fleet s (rear i _) _=_; rw [tip n (soar i f) (soar_lower _ _ h i) s hs i x y,fleet_cons' i (i ::ₘ s)]; rfl
-- multiset trace onto any homogeneous
private abbrev Flank := {i:Axis//i≠0}
set_option linter.unusedVariables false in
private def solveTr (b:Fliers→E)(t:Fliers): E:= if h: (0:Axis)∈t then
 let r:= t.erase (0:Axis)
 if H:(0:Axis)∈r then
   let s:= r.erase (0:Axis)
   b s-∑ i:Flank, solveTr b (i.val ::ₘ i.val ::ₘ s)
 else 0
 else 0
termination_by t.count (0:Axis)
decreasing_by
 have h₁:=Multiset.cons_erase h
 have h₂:= Multiset.cons_erase H
 have W₁:=congrArg (Multiset.count (0:Axis)) h₁
 have W₂:=congrArg (Multiset.count (0:Axis)) h₂
 have he:(0:Axis) ≠ i.val:= i.property.symm
 simp only [Multiset.count_cons_self] at W₁ W₂
 rw [Multiset.count_cons_of_ne he,Multiset.count_cons_of_ne he]; unfold r at W₂; omega
omit [Module ℝ E] in
lemma sol_tr (b:Fliers→E): ∃ c:Fliers→E,∀t:Fliers, (∑ i:Axis, c (i ::ₘ i ::ₘ t))=b t:=by
 let c:=solveTr b; refine ⟨c,fun t=>?_⟩
 have he : solveTr b (0 ::ₘ 0 ::ₘ t)= b t- ∑ i:Flank,solveTr b (i.val ::ₘ i.val ::ₘ t):=by rw [solveTr]; simp
 let X:=Finset.univ.erase (0:Axis)
 let f(i:Axis):=c (i ::ₘ i ::ₘ t)
 have hh : f 0=b t-∑ i ∈X,f i:=by
    refine he.trans ?_; congr 1
 change ∑i:Axis,f i=b t
 rw [←Finset.add_sum_erase _ _ (Finset.mem_univ (0:Axis)),hh]; exact sub_add_cancel ..
lemma solve_lap (n:ℕ)(f:Plane E)(hf:f∈cap E n): ∃v:Plane E,v∈cap E (n+2)∧lap v=f:=by
 induction n generalizing f with
 | zero=>rw [groundZero] at hf; have H:f=0:= hf; subst f; exact ⟨0,Submodule.zero_mem _,map_zero _⟩
 | succ n ih=>
   obtain ⟨b,hb⟩:=sol_tr (fun s=>fleet s f 0)
   obtain ⟨p,P,Q⟩:=peano (n+2) b; obtain ⟨q,H,K⟩ :=ih (f-lap p) (by
    intro s hs; rw [map_sub,sub_eq_zero]; funext x; rw [landed (member.mp hf) s hs x 0,lap_top n p P s hs x 0,←hb s]
    exact Finset.sum_congr rfl fun i _=>(Q _ (by simp [hs])).symm)
   refine ⟨p+q,Submodule.add_mem _ P (cap_succ _ H), ?_⟩; rw [map_add,K]; abel

abbrev Bevy (E:Type*) := Axis→ Plane E
def spanHull (E:Type*) [AddCommGroup E][Module ℝ E](m:ℕ): Submodule ℝ (Bevy E):= Submodule.pi Set.univ (fun _=> cap E m)
lemma in_hull{m:ℕ}{f:Bevy E}: f∈spanHull E m ↔ ∀i,f i∈ cap E m:=by simp [spanHull]
def incline: Plane E→ₗ[ℝ] Bevy E:=LinearMap.pi soar
def dive: Bevy E→ₗ[ℝ] Plane E:=∑ i:Axis,rear i ∘ₗ LinearMap.proj i -- uses comp
lemma dive_apply(f:Bevy E): dive f=∑ i,rear i (f i):=by simp [dive]
lemma dive_up(f:Plane E): dive (incline f)=lap f:=by rw [lap, LinearMap.sum_apply,dive_apply]; rfl
abbrev bend(f:Bevy E)(i j:Axis):Plane E:= soar i (f j)-soar j (f i)
lemma pitch (f:Bevy E)(j:Axis): ∑ i:Axis,rear i (bend f i j) = lap (f j) - soar j (dive f):=by
 rw [lap,LinearMap.sum_apply, dive_apply,map_sum]; simp only [soar_rear,bend,map_sub,Finset.sum_sub_distrib]; rfl
-- solution at this horizon
def team (E:Type*) [AddCommGroup E][Module ℝ E](m:ℕ): Submodule ℝ (Bevy E) where
 carrier:={f| f∈ spanHull E m ∧ dive f=0 ∧ ∀i,lap (f i)=0}
 zero_mem':=⟨Submodule.zero_mem _,map_zero _,fun _=>map_zero lap⟩
 add_mem':=by rintro f g ⟨a,b,c⟩ ⟨d,e,h⟩; exact ⟨Submodule.add_mem _ a d,by rw [map_add,b,e,add_zero],fun i=>by rw [Pi.add_apply,map_add,c,h,add_zero]⟩
 smul_mem':=by rintro k f ⟨a,b,c⟩; exact ⟨Submodule.smul_mem _ k a,by rw [map_smul,b,smul_zero],fun i=>by rw [Pi.smul_apply,map_smul,c,smul_zero]⟩
lemma lap_soar(f: Plane E)(i:Axis): lap (soar i f)=soar i (lap f):=by
 simp only [lap,LinearMap.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro j h; change rear j (soar j _) = soar i (rear j (soar j f)); rw [soar_rear,show soar i (soar j f)=soar j (soar i f) from LinearMap.congr_fun (comm i j) f]
lemma team_incline {m:ℕ}{f:Plane E}(he:f∈cap E (m+1))(hp:lap f=0) : incline f∈ team E m:=by
 refine ⟨in_hull.mpr (fun i=> soar_lower _ _ he i),(dive_up _).trans hp,fun i=>?_⟩; rw [incline,LinearMap.pi_apply, lap_soar,hp,map_zero]
lemma team_wing {n:ℕ}{f:Bevy E}(he:f∈team E n):∀i,f i∈cap E n:=in_hull.mp he.1
lemma team_height{n m:ℕ}(h:n≤m):team E n≤team E m:=fun _ hf=>⟨in_hull.mpr fun i=>cap_height h (team_wing hf i),hf.2⟩

end YM.SchemeRG11.Flock
