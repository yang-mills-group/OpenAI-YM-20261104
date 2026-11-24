import YM.WilsonCoeffUV.Wick.FiniteSplit
/-!
Exact finite lift of horizontal and zero harmonic row, no bound at ~larger periods asserted.
(This is specific to the full Wilson W precision, on translation-rotor and
any admitted momenta including p=small. Used to prove Wick readout identity.) -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Set Function Filter Lattice RG Laurent Exterior Bloch Metric Next.Free Precision
open Matrix FreeResolvent Blue
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {U:Type*}[Fintype U]
variable {G:Gauge}{j k m N:ℕ}{n:Side} {s:ℝ} (k':ℝ)(v:Train j)
omit [Fintype U] in
lemma up_f (n:Side){α β:Type}[Fintype α][Fintype β](W:Matrix U (Site n × α) ℂ)(D:Momentum → Matrix α β ℂ)(p:Site n):
    submatrix (W*solo n D) id (fun i:β=>(p,i))=(submatrix W id (fun i=>(p,i)))* D (mon p):=by
    ext i j; simp only [submatrix_apply,Matrix.mul_apply,Fintype.sum_prod_type,solo,fiber,Matrix.of_apply,id_eq, mul_ite,mul_zero]; simp
omit [Fintype U] in
lemma lows_f {u:Matrix U (Body 1 n) ℝ}(h:∀ i a,∑ j:Site n,u i (j,a)=0): submatrix (approached u * rotations n (TypeFace 1)) id (fun i=>(0,i))=0:= by
    ext i a; simp_rw [submatrix_apply,Matrix.mul_apply,Fintype.sum_prod_type,rotations]; simp [cell, approached, ← Complex.ofReal_sum,h]
lemma mount [DecidableEq U] (k:ℕ)(u:Matrix U (Body k n) ℝ) : Runs (1:Matrix U U ℂ) (rotations n (TypeFace k)) u (approached u*rotations n (TypeFace k)) := (Matrix.one_mul _).symm
-- use explicit zero paint and Kin
lemma stockLift (hk:0<k')(hj:4≤j){u:Matrix U (Body 1 n) ℝ}(hp:u*d 0 n=0)(h:∀ i a,∑ j:Site n,u i (j,a)=0) :
    u*unitStar k' v n* Precision.K ((record (pulse k' v)).acts n)=u:=by
    classical
    let F:= approached u * rotations n (TypeFace 1)
    have he:= mount (n:=n) 1 u
    have hx:= ((he.product (unitS_fiber k' v hk n)).product (runs_rotor k' hk hj v n))
    apply hx.lands _ (rotations_crew n _)
    have ht:Runs (1:Matrix U U ℂ) _ (u*d 0 n) (F*solo n (signal 1 0)):= he.product ((cobound_true 0).coarse n)
    have hv : F*solo n (signal 1 0)=0:= by
       unfold Runs at ht; rw [hp,Matrix.one_mul,show approached (0: Matrix U _ ℝ)=0 by ext; simp [approached],Matrix.zero_mul] at ht; exact ht.symm
    change Runs (1:Matrix U U ℂ) _ u (F*solo n (loomM k' v)*solo n (rotor 1 k' v))
    unfold Runs; rw [Matrix.one_mul]
    change F=_
    ext i ⟨p,a⟩
    let t:_:=submatrix F id (fun j=>(p,j)); change t i a=submatrix (F*solo n (loomM k' v)*solo n (rotor 1 k' v)) id (fun j:TypeFace 1=>(p,j)) i a
    rw [up_f,up_f]; change t i a=((t*loomM k' v (mon p))*rotor 1 k' v (mon p)) i a
    by_cases hh:p=0
    · have h0:t=0:=by unfold t; rw [hh]; exact lows_f h
      rw [h0,Matrix.zero_mul,Matrix.zero_mul]
    rw [Matrix.mul_assoc,loomM,if_neg (fun hz=> hh (mnode0.mp hz)),rotor_before _ _ hk _ (base_subset_realCube zone_pos (mon_mem n p)) (mt mnode0.mp hh),Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc t]
    rw [show t*signal 1 0 (mon p)=0 from (up_f n F (signal 1 0) p).symm.trans (by rw [hv]; rfl),Matrix.zero_mul,sub_zero]

lemma parallelW {P:Ten ℝ (Woods G n) (m+1)} (hk:0<k')(hj:4≤j)(Q:Fin m→Woods G n) (hp:∀ a, ∑ i:Woods G n,(tensor G (d 0 n)) i a*P (Fin.cons i Q)=0) (hh:∀ t:Hooks G,∑ i: Site n,P (Fin.cons (i,t) Q)=0) (i:Woods G n):
    ∑ b:Woods G n,(ColorStar k' v G n*precisionC G n (record (pulse k' v))) b i*P (Fin.cons b Q) =P (Fin.cons i Q):=by
    obtain ⟨x,b,a⟩:=i; let u:Matrix Unit (Body 1 n) ℝ:=of fun _ i=> P (Fin.cons (i.1,i.2,a) Q)
    let V:=unitStar k' v n*Precision.K ((record (pulse k' v)).acts n)
    have he : u*(d 0 n)=0:= by
       ext j s; cases s with | mk p i=>
        specialize hp (p,i,a); simp only [tensor,Fintype.sum_prod_type,Matrix.of_apply,ite_mul,zero_mul] at hp
        simpa [Matrix.mul_apply,u,Fintype.sum_prod_type,mul_comm] using hp
    have hx: u*V=u:= by
       unfold V; rw [← Matrix.mul_assoc]; exact stockLift k' v hk hj he (fun i t=> hh (t,a))
    have ht:= congr_fun (congr_fun hx Unit.unit) (x,b)
    rw [ColorStar,precisionC,← tensor_mul];
    change (∑ i:Woods G n,tensor G V i (x,b,a)*P (Fin.cons i Q))= P (Fin.cons _ Q)
    simpa [Matrix.mul_apply,u,Fintype.sum_prod_type,tensor,ite_mul,mul_comm] using ht
section
omit v k'
open Blue
variable {R:Type*}[CommSemiring R]
-- no tensor norm assertions needed. put ourselves in real
private lemma recount (K:Matrix U U ℝ)(T:Ten ℝ U k) (h:Blue.Smooth T)
    (p:∀ m:ℕ, (g:m+1=k) → ∀ x:Fin m→U,∀ i:U, ∑ j:U,K j i *(T ((Fin.cons j x) ∘ (finCongr g).symm))=T ((Fin.cons i x) ∘ (finCongr g).symm)):
    cord K (palms _ T) = palms _ T :=by
    induction k with
    | zero=> rw [shell T default];
             simp [cord]
    | succ k ih=>
       rw [sprouts]; simp_rw [map_sum,map_mul]
       have he i : cord K (palms _ (prune T i))=palms _ (prune T i):=by
           apply ih _ (h.prune i); intro m g x j; subst k
           have hh u: prune T i ((Fin.cons u x) ∘ (finCongr rfl).symm) = T ((Fin.cons u (Fin.cons i x)) ∘ (finCongr rfl).symm):= by
              exact congr_fun (prune_square h i u) x
           simp_rw [hh]; exact p _ rfl ..
       have hb i : ∑ j, K j i • prune T j=prune T i := by
          ext1 x; simp_rw [Finset.sum_apply]; exact p k rfl ..
       simp_rw [he,cord_var, Finset.sum_mul]; rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun i _=>?_ ;
       rw [← hb i];
       rw [map_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul]; simp [Algebra.smul_def]; ring
end
structure NullTop (T: Gen ℝ (Woods G n)): Prop where
    sense: Pure T
    finite: FiniteGen T
    stop m (Q:Fin m→Woods G n) a: ∑ i:Woods G n, (tensor G (d 0 n)) i a*T (m+1) (Fin.cons i Q)=0
    stand m (Q:Fin m→Woods G n) t: ∑ i: Site n,T (m+1) (Fin.cons (i,(t:Hooks G)) Q)=0
lemma canopied (hk:0<k')(hj:4≤j)(T: Gen ℝ (Woods G n))(h:NullTop T):
    cord (ColorStar k' v G n*precisionC G n (record (pulse k' v))) (totalR T)=totalR T:=by
    rw [visible h.finite.choose_spec,map_sum]; refine Finset.sum_congr rfl (fun i _=>?_); apply recount _ _ (h.sense _); intro m g x y; subst i; exact parallelW _ _ hk hj x (h.stop m x) (h.stand m x) y
end YM.WilsonCoeffUV.Bank.Carp
