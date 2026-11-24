import YM.OPE.Compatible.Mire.Music
/-!
# Top Kelvin lift and characteristic projections
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sagebrush
open Function MeasureTheory Set Topology Metric Filter Lattice Maxwell Extra.FD SphereTest Analysis Extra.FD.OPE
open scoped BigOperators Classical ContDiff
open Next.Rank.Radian (dV stroll)
variable {x:E4}{m j k:ℕ}{f g:E4→ℝ}{s:ℝ}
def gravy : List Axis→E4→ℝ
| []=>fun _=>normal
| a::l=>qRad*grad a (gravy l)-(2*((l.length:ℝ)+1)) • (coordF a*gravy l)
def nut (k:ℕ):ℝ := (-1:ℝ)^k*mash k*normal
lemma nut0:nut 0=normal:=by simp [nut,mash]
lemma nut_plus (k:ℕ):nut (k+1)=-(2*((k:ℝ)+1))*nut k:=by unfold nut mash; rw [pow_succ,pow_succ _ k,Nat.factorial_succ]; push_cast; ring
lemma pellet (l:List Axis):Spherical (gravy l) l.length:=by
    induction l with
    | nil=> exact ⟨⟨contDiff_const,fun _ _=>by simp only[List.length_nil,pow_zero,gravy,one_smul]⟩,lap_zero _⟩
    | cons a l ih=> exact radialRaise ih a
lemma taxes (hx:x∈away)(l:List Axis): dV l Green x=rr x^(l.length+1)*gravy l x:=by
    induction l generalizing x with
    | nil=> change normal*_=(rr _ ^(0+1))*normal; rw [zero_add,pow_one,mul_comm];rfl
    | cons i l ih=>
      let F:=gravy l; let m:= l.length; have hh: dV l Green=ᶠ[𝓝 x] rr^(m+1)*F:=by filter_upwards [open_away.mem_nhds hx] with y hy; exact ih hy
      change grad i (dV l Green) x=_; erw [(grad_won hh i).self_of_nhds, Gp _ F (show ContDiffAt ℝ ∞ (rr^(m+1)) x from (rr_smooth hx).pow _) (pellet l).size.smooth.contDiffAt, grad_power hx]
      change -(2*((m+1:ℕ):ℝ))*rr x^(m+1+1)* x i* F x+rr x^(m+1)*grad i F x=rr x^(m+1+1)*(qRad x*grad i F x-(2*((m:ℝ)+1))*(x i*F x)); have ht: rr x*qRad x=1:=inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)); rw [pow_succ (rr _) (m+1),mul_sub]; push_cast; rw [show rr x^(m+1)*rr x*(qRad x*grad i F x)=(rr x*qRad x)*(rr x^(m+1)*grad i F x) from by ring,ht]; ring
lemma chip (l:List Axis): gravy l=nut l.length • mon l ∨ ∃ k f, l.length=k+2 ∧ PureA k f ∧ gravy l=nut l.length • mon l+qRad*f:=by
    induction l with
    | nil=> left; apply funext; intro x; change normal=nut 0*_ ; rw [nut0]; change _ = normal * 1;ring
    | cons i l ih=>
      cases l with
      | nil=> left; apply funext; intro x; have he: grad i (fun _ : E4=> normal)=(0:E4→ℝ):=funext fun x=>by simp [grad,D]
              rw [gravy]; change qRad x*grad i (fun _:E4=> normal) x-(2*((↑(0:ℕ):ℝ)+1))*(coordF i x*normal)=nut (0+1)*(coordF i x*1); rw [he, nut_plus,nut0]; simp
              ring
      | cons a l=>
        let k:=l.length; let v:=a::l; have he:v.length=k+1:=rfl; let L:=nut (k+1); let x:=2*((k:ℝ)+2); have hp:PureA k (grad i (gravy v)):= (pellet v).size.derive i; have hx:nut (k+2)=-x*L:=by rw [nut_plus];unfold x L; push_cast; ring
        right; refine ⟨k,?_⟩; change gravy v=nut (k+1) • mon v ∨ _ at ih
        obtain H|⟨j,f,h,hf,hq⟩:=ih
        · refine ⟨_, rfl,hp,?_⟩; rw [gravy]; funext z; have H':=congrFun H z; change gravy v z=nut (k+1)*(mon v z) at H'; change qRad z* grad i (gravy v) z - (2*((↑(k+1:ℕ):ℝ)+1))*(coordF i z*gravy v z)=nut (k+2)*(coordF i z * mon v z) + _; erw [H',hx]; unfold x L; push_cast; simp only [Pi.mul_apply]; ring
        have hj : j+1=k:=by change k+1=j+2 at h;omega
        have hv:PureA k (coordF i*f):=by rw [←hj,add_comm]; exact pure_multiply (pure_coordF _) hf
        refine ⟨_, rfl,hp.minus (hv.vScale x), ?_⟩; rw [gravy]; funext z; have hv':=congrFun hq z; change gravy v z= L*mon v z+qRad z*f z at hv'; change qRad z*grad i (gravy v) z-(2*((↑(k+1:ℕ):ℝ)+1))*(coordF i z*gravy v z)=nut (k+2)*(coordF i z*mon v z)+ qRad z*(grad i (gravy v) z - x*(coordF i z*f z)); rw [hx,hv']; unfold x;push_cast;ring
lemma money_plus (l p: List Axis): mon (l++p)=mon l*mon p:=by
   induction l with
   | nil=> rw [mon,List.nil_append,one_mul]
   | cons a l ih=> rw [List.cons_append,mon,mon,ih,mul_assoc]
lemma loan_tag (l:List Axis)(hg:PureA m g) (hf:Spherical f k)(h:l.length+m=k): ends k (gravy l*g*f)=nut l.length * ends k (mon l*g*f):=by -- m binder
    obtain hh|⟨j,a,hx,ha,he⟩:=chip l
    · rw [hh, smul_mul_assoc,smul_mul_assoc,ends_scale k (show seg (mon l*g*f) from ((pureMon _).smooth.mul hg.smooth).mul hf.size.smooth)]; rfl
    obtain ⟨i,hk⟩:∃ i,k=i+1:=Nat.exists_eq_add_one.mpr (by omega)
    rw [hk] at h hf ⊢; rw [he,add_mul, add_mul, smul_mul_assoc,smul_mul_assoc]
    let A:= a*g; let B:=A*f; have hA:=pure_multiply ha hg; have hB:PureA (2*i) B:=by
         have ht:=pure_multiply hA hf.size; rw [show j+m+(i+1)=2*i from by omega] at ht; exact ht
    rw [show qRad*a*g*f=qRad • B from by change qRad*a*g*f=qRad*(a*g*f);ring, ends_add (i+1) (show seg (nut _ • (mon l*g*f)) from (((pureMon l).smooth.mul hg.smooth).mul hf.size.smooth).const_smul (nut l.length)) (show seg (qRad • B) from pure_square.smooth.mul hB.smooth), ends_scale _ (show seg (mon l*g*f) from ((pureMon _).smooth.mul hg.smooth).mul hf.size.smooth),lap_value i _ hB]; rw [show ends i B=0 from silence hA hf (by omega) (by omega)]; simp
-- projections
def tint (l:List Axis)(x:E4):=dV l Green x
def fineI (s:ℝ)(f:E4→ℝ):=∫ x, annA s x*f x
lemma fine_solo (hs:0<s)(l:List Axis)(hf:PureA k f)(hx:l.length=k+2): fineI s (tint l*f) =0:=by
   let Q:=gravy l; let j:=k+1; have hk:PureA (2*j) (f*Q):=by have ht:=pure_multiply hf (pellet l).size; rw [show k+l.length=2*j from by unfold j; omega] at ht; exact ht
   have hu:fineI s (tint l*f)=countM s j (f*Q):=by
       apply integral_congr_ae; filter_upwards with x; by_cases h:x=0; · subst x; rw [coldA.self_of_nhds];simp
       change annA s x*((dV l Green x)*f x)= _* _*(f x*Q x); rw [taxes h,hx]; unfold j Q;ring
   rw [hu,ladder hk hs,show ends j (f*Q)=0 from silence hf (pellet l) (by omega) (by unfold j; omega)];simp
lemma fine_duo (hs:0<s)(l p:List Axis)(hf:Spherical f (l.length+p.length)): fineI s (tint l*tint p*f)=
    countM s 0 1 /brim (l.length+p.length) *mash (l.length+p.length)*nut l.length*nut p.length*dV (l++p) f 0:=by
    let k:=l.length+p.length; let M:=gravy l*gravy p*f
    have hM:PureA (2*k) M:=by rw [two_mul]; exact pure_multiply (pure_multiply (pellet l).size (pellet p).size) hf.size
    rw [show fineI s (tint l*tint p*f)=countM s k M from ?_, ladder hM hs]; rotate_left
    · apply integral_congr_ae; filter_upwards with x; by_cases h:x=0; · subst x; rw [coldA.self_of_nhds]; simp
      change annA s x*(dV l Green x*dV p Green x*f x)= annA s x * rr x^(k+2)*M x; rw [taxes h,taxes h,show k+2=l.length+1+(p.length+1) by unfold k;omega,pow_add]; unfold M; simp only [Pi.mul_apply]; ring
    have ht:(l++p).length=k:=by simp [k]
    unfold M; rw [loan_tag l (pellet p).size hf rfl,mul_comm (mon l),loan_tag p (pureMon l) hf (add_comm ..),mul_comm (mon p),← money_plus, show ends (l.length+p.length) (mon (l++p)*f)=mash k*dV (l++p) f 0 from by change ends k _= _; rw [← ht]; exact roster _ (show Spherical f (l++p).length from ht.symm ▸ (show Spherical f k from hf))]; unfold k;ring
end YM.OPE.Sagebrush
