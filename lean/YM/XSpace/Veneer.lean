import YM.XSpace.Composing
/-! # Power-counted invariant lag stencils & battleground of derivative errors -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Relief
open Function Set Filter Lattice Trace Chiral Litter Pages Mu Tide Scale MvPolynomial Structure1 Sail
open scoped Topology BigOperators ContDiff
variable {n k d:ℕ}{G:Gauge}
abbrev Toe := Cover→ℝ
def Terrain (k:ℕ): Submodule ℝ Toe where
 carrier := {p| Glow k p}
 zero_mem':= Beam.zero.glows
 add_mem' := by
   rintro p q a b l; obtain ⟨C,hC,H⟩:=a l; obtain ⟨D,hD,K⟩:=b l; refine ⟨C+D,by positivity,fun x=>?_⟩; rw [← peaked,map_add,Pi.add_apply,peaked,peaked,add_mul]; exact (norm_add_le ..).trans (add_le_add (H x) (K x))
 smul_mem':= by
   rintro v p a l; obtain ⟨C,hC,H⟩:= a l; refine ⟨‖v‖*C,by positivity,fun x=>?_⟩; rw [← peaked,map_smul,Pi.smul_apply,peaked,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (H x) (norm_nonneg _)
abbrev D (a:Axis) := teeth (F:=ℝ) a
abbrev mov (u:Cover) := sweep (F:=ℝ) u
abbrev η (a:Axis):= rat (F:=ℝ) a
variable {f:Toe}
lemma steady (h:f∈Terrain k): Glow k f:=h
lemma virgin (h:f∈Terrain k):∃ C:ℝ,0<C∧∀ x:Cover, |f x| ≤ C*carry k (reach x):=by obtain ⟨C,hC,H⟩:=steady h []; refine ⟨C+1,by positivity,fun x=>(H x).trans ?_⟩; exact mul_le_mul_of_nonneg_right (by simp) (carry_pos ..).le
lemma backs {f:Toe}(x:Cover)(a:Axis): mov x f= mov (x+Lattice.step a) f-mov x (D a f):=by
  funext z; change f (x+z)=f (x+ Lattice.step a+z)- (f (x+z+Lattice.step a)-f (x+z)); rw [add_right_comm x]; abel
lemma D_move (f:Toe)(x:Cover)(i:Axis): D i (mov x f)=mov x (D i f):= tooth_sweep ..
lemma step_comm (f:Toe)(a b:Axis): D a (D b f)= D b (D a f):=by funext y; change f (y+step a+ step b)-_ -(_-_) = f (y+step b+step a)-_ -(_-_); rw [add_right_comm y]; change _-f (y+step a)-(f (y+step b)-f y)=_-f (y+step b)-(f (y+step a)-f y); abel
lemma down_phase {f:Toe}(i:Axis): η i f= -(mov (-step i) (D i f)):=by
  ext1 y; rw [Pi.neg_apply]; change η i f y= -(teeth (F:=ℝ) i f (-step i+y)); rw [rat_step]; rw [add_comm,sub_eq_add_neg]
lemma dual_plus {f:Toe}(x y:Cover): mov x (mov y f)=mov (y+x) f:=by ext1 z; change f (y+(x+z))=_; rw [← add_assoc];rfl
@[simp] lemma mov0 (f: Toe): mov 0 f=f:= by ext1 i; change f (0+i)=_; simp only [zero_add]
lemma downhill (x:Axis){p:Toe} : D x (mov (-step x) p)= -η x p :=by rw [D_move, down_phase,neg_neg]
lemma light_hill (t:ℕ)(h:t≤ k): Terrain k ≤ Terrain t:= by
  intro p hp; change Glow _ p; intro l; obtain ⟨C,hC,H⟩:= steady hp l; exact ⟨C,hC,fun x=>(H x).trans (mul_le_mul_of_nonneg_left (carry_weight _ (by omega)) hC)⟩
lemma slide_hill (h:f∈Terrain k)(y:Cover): mov y f∈ Terrain k:=by
  change Glow k _; intro l; obtain ⟨C,hC,H⟩:= steady h l; refine ⟨C*(1+(reach y:ℝ))^(k+l.length),by positivity,fun x=>?_⟩; rw [peak_move]; apply (H (y+x)).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hC; apply phase_cost; rw [← reach_neg y,add_comm y]; exact le_trans (le_of_eq (show reach x=reach (x+y+-y) by rw [add_neg_cancel_right])) (tree ..)
lemma steps_hill (h:f∈Terrain k) (d:Axis): D d f ∈ Terrain (k+1):=by change Glow _ _; intro l; have he:= steady h (d::l); rw [snack] at he; simp_rw [show k+1+l.length=k+(d::l).length from (by simp; omega)]; exact he
lemma down_hill (h:f∈Terrain k)(d:Axis):η d f ∈ Terrain (k+1):= by rw [down_phase]; exact Submodule.neg_mem _ (slide_hill (steps_hill h d) _)
lemma hill2 : Sail.cover ∈ Terrain 2:= greenBeam.glows
-- to perform IBP need membership in one explicit module reserve (all directions)
def Surface (k:ℕ): Submodule ℝ Toe:= ⨆ i:Axis, (Terrain k).map (D i)
lemma surface (h:f∈Terrain k)(i: Axis): D i f∈ Surface k:=(le_iSup (fun i:Axis=> (Terrain k).map (D i)) i) (Submodule.mem_map_of_mem h)
lemma surfaces : Surface k≤ Terrain (k+1):= by refine iSup_le fun i=>?_ ; rintro f ⟨f,h,rfl⟩; exact steps_hill h i
lemma surfaces_p (V:Submodule ℝ Toe)(h: ∀ f∈Terrain k,∀ i:Axis, D i f∈V): Surface k ≤ V:=by refine iSup_le fun i=>?_ ; rintro f ⟨f,hg,rfl⟩; exact h f hg i
lemma society (h:f∈Surface k)(x:Cover): mov x f∈ Surface k:= surfaces_p ((Surface k).comap (mov x)) (fun p hp i=> by change mov x (D i p)∈ Surface k; rw [← D_move]; apply surface (slide_hill hp _)) h
lemma steps_deriv (h:f∈Surface k)(x:Axis): D x f∈ Surface (k+1):= surface (surfaces h) x
lemma drip (H:f∈Terrain k)(i:Axis): η i f∈ Surface k:=by rw [down_phase]; exact Submodule.neg_mem _ (society (surface H i) _)
lemma safekeeping (h:f∈Terrain k)(x:Cover): mov x f-f∈Surface k:=by
  have he (p:Cover)(a:Axis): mov (p+step a) f-mov p f∈ Surface k:=by rw [show mov (p+step a) f-mov p f=mov p (D a f) from sub_eq_iff_eq_add.mpr (show _=_+_ by rw [eq_sub_iff_add_eq.mp (backs (f:=f) p a)|>.symm]; abel)]; exact society (surface h a) _
  generalize ht:Next.Rank.Beamer.street x=n; induction n generalizing x with
  | zero=> obtain h|⟨z,hz,_⟩:=past_stepping x; simp [h]; omega
  | succ n ih=>
    obtain h|⟨z,hz,h',a,H⟩:=past_stepping x; simp [h]; rw [← sub_add_sub_cancel (mov x f) (mov z f)]; refine Submodule.add_mem _ ?_ (ih z (by omega)); rcases H with H|H
    · rw [H]; apply he
    rw [H, ← neg_sub]; exact Submodule.neg_mem _ (he x a)
lemma derivative_forth (h:f∈Terrain k)(a b:Axis): D a (η b f)- D b (η a f) ∈ Surface (k+2):= by
  rw [down_phase,down_phase]; simp_rw [map_neg,D_move, step_comm f a b]; rw [neg_sub_neg]; set P:=D b (D a f); have hp:P∈ Terrain (k+2):=steps_hill (steps_hill h a) _; rw [← sub_sub_sub_cancel_right _ _ P]; exact Submodule.sub_mem _ (safekeeping hp _) (safekeeping hp _)
end YM.XSpace.Relief
