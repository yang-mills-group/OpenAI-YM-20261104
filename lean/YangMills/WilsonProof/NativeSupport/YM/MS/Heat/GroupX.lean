import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Quad
/-!
# One cycle at a point, before moving the integration variable

Keep LR & RL as two kernels B_R,L, converts at trc(...).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux
variable {R A P I: Type}[AddCommGroup P][CommRing R][Fintype A]{p:Sector A}{b c: Bool}
variable {K L:Flux A P R}{F H:Row A P R}{l r:Legs (Mode A P)}
def rMap (p:Sector A)(K:Flux A P R)(i j:A)(l r:Legs (Mode A P)) : Row A P R →ₗ[R] Row A P R →ₗ[R] R where
   toFun F:= { toFun := fun H=> radius p K i j F H l r
               map_add' _ _ := by simp [radius,mul_add]
               map_smul' x _:= by simp [radius, mul_left_comm x] }
   map_add' F H:= LinearMap.ext (fun _=> by simp [radius,mul_add,add_mul])
   map_smul' x F:= LinearMap.ext (fun _=> by simp [radius,mul_left_comm x] ; ring)
lemma summ_sum (F:A→A→A→A→R): (∑ a,∑ i,∑ b,∑ j,F a i b j)=∑ b,∑ j,∑ a,∑ i,F a i b j:= by
    have he := Finset.sum_comm (f:= fun (x y:A×A)=> F x.1 x.2 y.1 y.2) (s:=Finset.univ) (t:=Finset.univ); simpa only [Fintype.sum_prod_type] using he
omit [AddCommGroup P] in
lemma segmentL (p:Sector A)(w:List (Mode A P))(F: A→ Shared (Mode A P) R): (∑ i,scatter (field p) w (F i))=scatter (field p) w (∑ i,F i):= (map_sum (allocate ..) _ _).symm

def pairedX (p:Sector A)(K L:Flux A P R)(F H:Row A P R)(w:Legs (Mode A P))(q:P):R := scatter (field p) w (fun l r=> ∑ a,∑ e,∑ i,∑ j,(hits p K L F H l r a e i j q+ restL p K L F H l r a e i j q)) -- check precedence
lemma tierX (he:b=false ∨ c=false)(hp:closed K p b)(hL:closed L p c)(h: Reverse K p)(w:Legs (Mode A P))(q:P)(hf:Symm (field p) F)(hh:Symm (field p) H)(hx:Pure (field p) false F) : trc L q (tree p K F H) w=tree p K (trc L q F) H w + tree p K F (trc L q H) w + pairedX p K L F H w q:= by
   unfold tree; simp_rw [at_trc,scatter_cons]
   let T:=allocate (field p) w (R:=R)
   let f a e l r:= attaches p K F H ((a,q)::(e,-q)::l) r+cross (p a) (degree (field p) ((e,-q)::l))*attaches p K F H ((e,-q)::l) ((a,q)::r)+ cross (p e) (degree (field p) l)*(attaches p K F H ((a,q)::l) ((e,-q)::r) + cross (p a) (degree (field p) l)*attaches p K F H l ((a,q)::(e,-q)::r))
   let B : Shared (Mode A P) R:= fun l r=>∑ a,∑ e,∑ i,∑ j,(hits p K L F H l r a e i j q+restL p K L F H l r a e i j q);
   change (∑ a,∑ e,L a e q • (T (f a e)))= T _ + T _ + T B;
   simp_rw [← map_smul,← map_sum, ← map_add]; apply LinearMap.congr_arg; ext l r
   simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply,f,B,smul_eq_mul, convertR h]; simp_rw [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
   let A0 a e i j l r:= radius p K i j (L a e q • diffPair (a,q) (e,-q) F) H l r; let Ac a e i j l r := radius p K i j F (L a e q • diffPair (a,q) (e,-q) H) l r;
   have h1 j₁ j₂ (F H:Row A P R): radius p K j₁ j₂ (trc L q F) H l r=∑ a,∑ e,radius p K j₁ j₂ (L a e q • diffPair (a,q) (e,-q) F) H l r:=by
     simp_rw [trc, LinearMap.sum_apply, LinearMap.smul_apply, show ∀ i:Row A P R,radius p K j₁ j₂ i H l r=(rMap p K _ _ l r).flip H i from fun _=>rfl,map_sum] -- replace
   have h2 i j : radius p K i j F (trc L q H) l r =∑ a,∑ e,radius p K i j F (L a e q • diffPair (a,q) (e,-q) H) l r:= by
     simp only [trc,LinearMap.sum_apply,LinearMap.smul_apply]; simp_rw [show ∀ H: Row A P R,radius p K i j F H l r=rMap p K i j l r F H from fun _=>rfl,map_sum]
   unfold hits restL; simp_rw [Finset.mul_sum, LL he hp hL _ _ _ _ _ hf, RR he hp hL _ _ _ _ _ hh hx, h1,h2]; 
   conv_rhs => lhs; lhs; rw [summ_sum]
   conv_rhs => lhs; rhs; rw [summ_sum]
   abel
end YM.MS.Heat
