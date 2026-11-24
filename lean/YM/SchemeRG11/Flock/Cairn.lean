import YM.SchemeRG11.Plate.Cost
/-!
Multiset difference geometry. `cap n` means strictly below n. Lattice polynomials,
all exact degrees before introducing norms. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Flock
open Function Lattice
abbrev Fliers:= Multiset Axis
abbrev Plane (E:Type*):= Cover→E
variable {E F:Type*} [AddCommGroup E][AddCommGroup F][Module ℝ E][Module ℝ F]
def hop (a:Cover): Module.End ℝ (Plane E) where
 toFun f x:= f (x+a)
 map_add' _ _:= rfl
 map_smul' _ _:=rfl
abbrev soar (a:Axis): Module.End ℝ (Plane E):= hop (step a)-1
lemma soar_apply(a:Axis)(f:Plane E)(x:Cover): soar a f x=f (x+step a)-f x:=rfl
lemma ascend (a:Axis)(f:Plane E)(x:Cover): f (x+step a)=f x+soar a f x:=by rw [soar_apply]; abel
lemma comm (a b:Axis): Commute (soar (E:=E) a) (soar b):=by apply LinearMap.ext; intro f; funext x; change soar a (soar b f) x=_; change _=soar b (soar a f) x; rw [soar_apply,soar_apply,soar_apply,soar_apply,soar_apply,soar_apply,add_right_comm x]; abel
def fleet (f:Fliers):Module.End ℝ (Plane E):= (f.map soar).noncommProd (fun i (h:_∈_) j (k:_∈_) _=>by obtain ⟨a,_,rfl⟩:= Multiset.mem_map.mp h; obtain ⟨b,_,rfl⟩:=Multiset.mem_map.mp k; exact comm ..)
lemma fleet_cons(i:Axis)(a:Fliers): fleet (E:=E) (i ::ₘ a)=soar i * fleet a:= by simp only [fleet,Multiset.map_cons,Multiset.noncommProd_cons]
lemma fleet_zero : fleet (E:=E) 0=1:=rfl
lemma fleet_cons'(i:Axis)(a:Fliers): fleet (E:=E) (i ::ₘ a)=fleet a*soar i:= by
 induction a using Multiset.induction with
 | empty=>rw [fleet_cons,fleet_zero]; simp
 | cons j s ih=>rw [Multiset.cons_swap, fleet_cons j,ih,fleet_cons,mul_assoc]
lemma flight (s t:Fliers): fleet (E:=E) (s+t)=fleet s*fleet t:=by
 induction s using Multiset.induction with
 | empty=>rw [zero_add,fleet_zero,one_mul]
 | cons i a ih=>simp only [Multiset.cons_add, fleet_cons, ih,mul_assoc]
lemma jump (s:Fliers)(f:Plane E)(v x:Cover): fleet s (hop v f) x=fleet s f (x+v):=by
 induction s using Multiset.induction generalizing x with
 | empty=> rfl
 | cons i a ih=> rw [fleet_cons]; change soar i _ _= soar i _ _; rw [soar_apply,soar_apply,ih,ih,add_right_comm]
lemma landed {n:ℕ}{f:Plane E}(hp: ∀ s:Fliers,s.card=n+1→fleet s f=0)(t:Fliers)(ht:t.card=n)(x y:Cover): fleet t f x=fleet t f y:=by
 have he (i:Axis)(x:Cover): fleet t f (x+step i)=fleet t f x:=by
    rw [ascend _ (fleet t f)]; have h:soar i (fleet t f) =0:=by have h:=hp (i ::ₘ t) (by simp [ht]); rw [fleet_cons] at h; exact h
    rw [h]; exact add_zero _
 have hz (w:Walk)(x:Cover):fleet t f (stop x w)=fleet t f x:=by
    induction w generalizing x with
    | nil=> rfl
    | cons a w ih=>
       rw [stop,ih]; rcases a with ⟨i,b⟩; cases b
       · exact he i x
       have hh :=he i (x-step i); rw [sub_add_cancel] at hh; change fleet t f (x + (-step i))=_; simpa only [sub_eq_add_neg] using hh.symm
 rw [←route_end x y 1]; exact (hz ..).symm
def cap (E:Type*) [AddCommGroup E][Module ℝ E](n:ℕ):Submodule ℝ (Plane E) where
 carrier :={f|∀s:Fliers,s.card=n→fleet s f=0}
 zero_mem' :=fun _ _=>map_zero _
 add_mem':=by rintro x y hx hy v h; rw [map_add,hx v h,hy v h,add_zero]
 smul_mem':=by rintro c x hx v h;rw [map_smul,hx v h,smul_zero]
lemma member {n:ℕ}{f:Plane E}:f∈cap E n ↔ ∀s:Fliers,s.card=n→fleet s f=0:= Iff.rfl
lemma groundZero : cap E 0=⊥:=by apply bot_unique; intro f hf; exact member.mp hf 0 rfl
lemma cap_succ(m:ℕ):cap E m≤cap E (m+1):=by
 intro f hf t w; induction t using Multiset.induction with
 | empty=>simp at w
 | cons i a=>rw [fleet_cons]; change soar i _ =_; rw [member.mp hf a (by simpa using w),map_zero]
lemma cap_height{m n:ℕ}(h:m≤n):cap E m≤cap E n:= monotone_nat_of_le_succ cap_succ h
lemma soar_lower (m:ℕ)(f:Plane E)(h:f∈cap E (m+1))(i:Axis): soar i f∈cap E m:=by
 intro t w; have he:=member.mp h (i ::ₘ t) (by simp [w]); rw [fleet_cons'] at he; exact he
lemma jump_flat (f:Plane E)(s:Fliers)(hf:f∈cap E (s.card+1))(x y: Cover): fleet s f x=fleet s f y:=landed (member.mp hf) _ rfl x y
lemma hop_cap {m:ℕ}{f:Plane E}(hf:f∈cap E m)(x:Cover):hop x f∈cap E m:=by
 intro t h; funext y; rw [jump,member.mp hf _ h];rfl
lemma flights_zero {n:ℕ}{f:Plane E}(hf:f∈cap E n)(he:∀ t:Fliers,t.card<n→fleet t f 0=0): f=0:=by
 induction n with
 | zero=> rw [groundZero] at hf; exact hf
 | succ n ih=>
   apply ih _ fun t ht=>he t (by omega)
   intro t h; funext y; exact (landed (member.mp hf) _ h y 0).trans (he t (by omega))
abbrev Mob (n:ℕ) := (k:Fin n) × Sym Axis k.val
def formation(n:ℕ): Plane E →ₗ[ℝ] (Mob n→E):=LinearMap.pi (fun v=> LinearMap.proj (φ:=fun _:Cover=> E) 0 ∘ₗ fleet v.2.val)
instance bounded(n:ℕ)[FiniteDimensional ℝ E]:FiniteDimensional ℝ ↥(cap E n):=FiniteDimensional.of_injective (formation n ∘ₗ (cap E n).subtype) (by
 apply LinearMap.ker_eq_bot.mp; refine LinearMap.ker_eq_bot'.mpr ?_; intro m h; apply Subtype.ext; apply flights_zero m.property; intro t ht; exact congrFun h ⟨⟨t.card,ht⟩,⟨t,rfl⟩⟩)
lemma soaring_map(L:E→ₗ[ℝ] F)(f:Plane E)(i:Axis):soar i (L ∘ f) = L ∘ (soar i f):=by funext x; exact (L.map_sub _ _).symm
lemma plane_map(L:E→ₗ[ℝ] F)(f:Plane E)(s:Fliers): fleet s (L ∘ f) = L ∘ fleet s f:=by
 induction s using Multiset.induction with
 | empty=>rfl
 | cons i a ih=>rw [fleet_cons,fleet_cons]; change soar i _=L ∘ soar i _; rw [ih,soaring_map]
                                                                                --
end YM.SchemeRG11.Flock
