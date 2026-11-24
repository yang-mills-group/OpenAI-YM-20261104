import YM.MSbar.Grass.Master

/-! Linear color/BRST substitution. Need finiteness for each *row*, even if infinitely many modes.
The superderivation on shuffle respects the orientation of the input word, not dual ordering. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset
open scoped BigOperators Classical
variable {T:Type*}{p:T→Bit} {f g h : Series T}{x y:T} {d e r k j : Bit}

structure Transport (p:T→Bit)(d:Bit) where
   coeff (b:T) : T→₀ℂ
   parity (b:T)(a:T) (he:a∈ (coeff b).support): p a= p b+d
namespace Transport
variable (A:Transport p d)
def row (b:T) : Order T := ∑ v∈(A.coeff b).support,(A.coeff b v) • field v
def act (v : word T) : Series T →ₗ[ℂ] ℂ:= match v with
    | [] => 0
    | a::l => (LinearMap.proj l).comp (A.row a) + sign d (p a) • ((act l).comp (field a))
def lift : Order T:= LinearMap.pi fun v=> A.act v
lemma cost (v:T) : A.row v f = ∑ i∈(A.coeff v).support,A.coeff v i • field i f :=by simp [row,LinearMap.sum_apply]
lemma base : A.lift f []=0:=rfl
lemma leg (a:T): field a (A.lift f)= A.row a f+ sign d (p a) • A.lift (field a f):=by funext v;change A.act (a::v) f=_; rw [act]; rfl
lemma row_h (hf:Homogeneous p k f) (a:T): Homogeneous p (p a+(d+k)) (A.row a f):=by
   rw [cost]; refine Homogeneous.sum fun i hi=> Homogeneous.scaling _ ?_
   have h := hf.derives i; rw [A.parity _ _ hi,add_assoc] at h; exact h
lemma row_move (hf:Homogeneous p k f) (a b:T): field b (A.row a f)= sign (p a+d) (p b) • A.row a (field b f):=by
   simp_rw [cost,map_sum,map_smul,Finset.smul_sum]; refine Finset.sum_congr rfl fun x hx=> ?_
   rw [hf.comm x b,A.parity _ _ hx,smul_comm]
lemma manages (h:Homogeneous p k f) : Homogeneous p (d+k) (A.lift f):=by
   -- support then sym
   constructor
   · intro v a b u; induction v generalizing k f with
     | nil =>
        change field b (field a (A.lift f)) u=sign (p a) (p b)*field a (field b (A.lift f)) u
        rw [leg,leg,map_add,map_add,map_smul,map_smul,leg,leg,A.row_move h,A.row_move h,h.comm a b,map_smul]
        simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sign_add]; rw [braid (p b) (p a)]
        rcases (show ∀ z:T, sign (p a) (p z)=1∨sign (p a) (p z)=-1 from fun z=> by unfold sign;split_ifs <;> simp) b with h'|h' <;> rw [h'] <;> ring
     | cons z v ih=>
        change field z (A.lift f) (v++_)=sign (p a) (p b)*field z (A.lift f) (v++_)
        rw [leg]; simp_rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; rw [(A.row_h h _).commute v a b,ih (h.derives _)]; ring
   intro v hv; induction v generalizing k f with
   | nil => apply base
   | cons a v ih=>
      change field a (A.lift f) v=0
      have hp : oddity p v≠p a+(d+k):= fun he=> hv (by rw [oddity_cons,he,cycle]); rw [leg,Pi.add_apply, Pi.smul_apply, (A.row_h h a).shape v hp, ih (h.derives _),smul_zero,zero_add]; simpa [add_left_comm d] using hp
lemma fee (hf:Homogeneous p k f)(a:T) (g:Series T): A.row a (join p f g)= join p (A.row a f) g+ sign (p a+d) k • join p f (A.row a g):= by
   simp_rw [cost,join_sum_left,join_sum_right,join_scale_left,join_scale_right,Finset.smul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro x hx; rw [product_rule hf.shape,A.parity _ _ hx,smul_add, smul_comm]
lemma derivation (hf:Homogeneous p k f)(hg:Homogeneous p j g): A.lift (join p f g)=join p (A.lift f) g+sign d k • join p f (A.lift g):=by
   funext v; induction v generalizing k j f g with
   | nil => simp [join,base]
   | cons a v ih =>
      change field a (A.lift _) v=(field a (join p (A.lift f) g)) v+sign d k*field a (join p f (A.lift g)) v
      rw [leg,A.fee hf,product_rule (A.manages hf).shape,product_rule hf.shape g,product_rule hf.shape (A.lift g),map_add,map_smul,leg,leg]
      simp only [join_add_left,join_scale_left,join_add_right,join_scale_right,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      have h1 := ih (hf.derives a) hg; have h2 := ih hf (hg.derives a) -- a
      rw [h1,h2]; simp only [Pi.add_apply, Pi.smul_apply,smul_eq_mul, sign_add_right, sign_add]; rw [braid (p a) d]; rcases (show sign d (p a)=1∨sign d (p a)=-1 from (by unfold sign;split_ifs <;> simp)) with h|h <;> rw [h] <;> ring
end Transport
end YM.MSbar.Super
