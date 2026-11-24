import YM.SchemeRG11.Flock.Eider
/-! Filtered gradient lifts, needed to test exact cover gauge Ward, not
 continuum-leading Ward alone. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Flock
open Function Lattice
variable {E F:Type*} [AddCommGroup E][AddCommGroup F][Module ℝ E][Module ℝ F]
open scoped Classical
-- vanish symbol condition shorthand (empty m=0)
abbrev skim (m:ℕ)(f:Bevy E):Prop:=∀i j:Axis,∀s:Fliers,s.card+1=m→ fleet s (bend f i j) 0=0
lemma agreement (m:ℕ)(f:Bevy E)(h:skim m f)(i j:Axis)(u v:Fliers)(hu:u.card=m)(he:i ::ₘ u=j ::ₘ v): fleet u (f i) 0=fleet v (f j) 0:=by
 rcases eq_or_ne i j with r|r
 · subst j; rw [show u=v from by simpa using he] -- check
 have hj:j∈u:= by
     have H:j∈i ::ₘ u:=by rw [he]; simp
     exact (Multiset.mem_cons.mp H).resolve_left r.symm
 obtain ⟨s,rfl⟩:=Multiset.exists_cons_of_mem hj
 rw [Multiset.cons_swap] at he
 rw [← show i ::ₘ s=v from by simpa using he] -- check
 have hk:=h j i s (by simpa using hu)
 unfold bend at hk; rw [map_sub,Pi.sub_apply] at hk
 rw [fleet_cons' j s,fleet_cons' i s]; exact sub_eq_zero.mp hk
lemma same_top (m:ℕ)(f:Bevy E)(he:f∈team E (m+1))(hb:skim m f): ∃p:Plane E,p∈cap E (m+2)∧ f-incline p ∈ spanHull E m:=by
 have h (t:Fliers): ∃ c:E,∀i s,i ::ₘ s=t→t.card=m+1→fleet s (f i) 0=c:=by
    induction t using Multiset.induction with
    | empty=> exact ⟨0,fun _ _ _ h=>by simp at h⟩
    | cons i t=> exact ⟨fleet t (f i) 0,fun j s e z=> agreement m f hb j i s t (by simpa [←e] using z) e⟩
 choose c hc using h; obtain ⟨p,P,Q⟩:= peano (m+1) c
 refine ⟨p,P,in_hull.mpr ?_⟩; intro i t H; rw [Pi.sub_apply,map_sub,sub_eq_zero]; funext x
 change fleet t _ _=fleet t (soar i p) x; rw [landed (member.mp (team_wing he i)) t H _ 0, show fleet t (soar i p)=fleet (i ::ₘ t) p from by rw [fleet_cons'];rfl, landed (member.mp P) _ (by simp [H]) _ 0,Q _ (by simp [H])]; exact hc _ i t rfl (by simp [H])
lemma dive_cap (m:ℕ)(f:Bevy E)(he:f ∈spanHull E (m+1)): dive f∈ cap E m:=by rw [dive_apply]; exact Submodule.sum_mem _ fun i _=> rear_low _ _ (in_hull.mp he i) _
lemma team_exact (m:ℕ)(f:Bevy E)(he:f∈team E (m+1))(hb:skim m f):∃p:Plane E,p∈cap E (m+2)∧lap p=0∧f-incline p∈team E m:=by
 obtain ⟨p,P,Q⟩:=same_top _ _ he hb
 have hh : ∃v:Plane E,v∈cap E (m+2)∧lap v=0∧ f-incline v∈spanHull E m:=by
    cases m with
    | zero=>
      have hx:f-incline p=0:=funext fun i=>by have h:=in_hull.mp Q i; rw [groundZero] at h; exact h
      refine ⟨p,P, ?_, Q⟩; rw [← dive_up,←sub_eq_zero.mp hx]; exact he.2.1
    | succ m=>
      obtain ⟨q,H,K⟩:=solve_lap m (dive (f-incline p)) (dive_cap m _ Q)
      refine ⟨p+q,Submodule.add_mem _ P (cap_succ _ H),?_,?_⟩
      · rw [map_add,K,map_sub, dive_up,show dive f=0 from he.2.1]; abel
      rw [map_add,←sub_sub]; apply Submodule.sub_mem _ Q; apply in_hull.mpr; intro i; exact soar_lower _ q H i
 obtain ⟨v,V,K,H⟩:=hh; have w : f-incline v∈ team E (m+1):= Submodule.sub_mem _ he (team_incline V K)
 exact ⟨v,V,K,H,w.2⟩
instance followers (n:ℕ)[FiniteDimensional ℝ E]:FiniteDimensional ℝ ↥(team E n):= by
 let L:team E n→ₗ[ℝ] (Axis→cap E n):=LinearMap.pi (fun i=> LinearMap.codRestrict (cap E n) (LinearMap.proj i ∘ₗ (team E n).subtype) fun x=>team_wing x.property i)
 exact FiniteDimensional.of_injective L fun _ _ h=>Subtype.ext (funext fun i=>congrArg Subtype.val (congrFun h i))
lemma dive_linear (L:E→ₗ[ℝ] F)(f:Bevy E): dive (fun i=>L ∘ f i) = L ∘ dive f:=by rw [dive_apply,dive_apply]; funext x; simp only [comp_apply,Finset.sum_apply,map_sum,rear_apply,L.map_sub]
lemma lap_linear (L:E→ₗ[ℝ] F)(f:Plane E): lap (L ∘ f)=L ∘ lap f:=by rw [← dive_up,← dive_up, ← dive_linear]; congr 1; funext i; exact soaring_map ..
lemma team_linear(L:E→ₗ[ℝ] F)(f:Bevy E)(n:ℕ)(h:f∈team E n): (fun i=>L ∘ f i)∈team F n:=by
 refine ⟨in_hull.mpr (fun i s hs=>funext fun x=>by rw [plane_map,member.mp (team_wing h i) _ hs]; exact map_zero _),?_,?_⟩
 · rw [dive_linear, show dive f=0 from h.2.1]; exact funext fun _=>map_zero _
 intro i; rw [lap_linear,show lap (f i)=0 from h.2.2 i]; exact funext fun _=>map_zero _
end YM.SchemeRG11.Flock
