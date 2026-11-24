import YM.RegulatorIR.Pupil.Nixes

/-!
# Extract simple-axis Rules at rank two
This is in real-color Fourier convention, unaffected by higher Poly prices.
Spell the lattice divergence signs. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G : Gauge}{U:Orders (Foot G)} {W: Type}{p e r:ℕ}

def tol (x:Cover)(w:Long W):Long W:=(dis x w.1,w.2)
def Throughout (T:Packet (Long W) r):Prop:=∀ x p,T (tol x ∘ p)=T p
def twin (T:Packet (Foot G) 2)(a b:Foot G):ℝ:= T ![a,b]
def sparkle (T:Packet (Foot G) 2)(x y:Edge Cover)(a b:G.Color):= ∑ i:G.ColorIndex,∑ j:G.ColorIndex,a i*b j*twin T (x,i) (y,j)
def sign (p:Signed)(v:Axis):ℝ:= if p.flip v then -1 else 1
def shore (p:Signed)(w:Long W):Long W:=(rotateE p w.1,w.2)
structure Rules (T:Packet (Foot G) 2) : Prop where
 twinSym (x y:Foot G) : twin T x y=twin T y x
 throughout : Throughout T
 pearl (k:G.El) (x y:Edge Cover)(a b:G.Color): sparkle T x y a b=sparkle T x y (G.adjoint k a) (G.adjoint k b)
 glow (p:Signed)(x y:Foot G) : twin T (shore p x) (shore p y)=sign p x.1.2*sign p y.1.2*twin T x y
 diverge (x:Foot G)(v:Cover)(j:G.ColorIndex): (∑ i:Axis,(twin T x ((v,i),j)-twin T x ((v-step i,i),j)))=0 -- binder ambiguity
lemma pairT {I:Type}(T:Packet I 2) -- I implicit
  (a b:I→ℝ) : chargeT T ![a,b] = ∑' z:I×I,T (![z.1,z.2])* (a z.1*b z.2):=by
 unfold chargeT; rw [← (twosM I).tsum_eq];apply tsum_congr;intro i; rw [Fin.prod_univ_two];rfl
lemma pairMatch (T:Packet (Foot G) 2) (a b:BEdge G) : matchT T ![a,b]= ∑' z:Foot G×Foot G,twin T z.1 z.2*(hue a z.1*hue b z.2):=by
 unfold matchT twin; rw [← pairT]; apply congr_arg; ext1 i;fin_cases i <;> rfl
lemma rangeT (T:Packet (Foot G) 2)(a b:G.Color)(x y:Edge Cover): matchT T ![lone x a,lone y b]= sparkle T x y a b:=by
 rw [pairMatch]
 let f (p:G.ColorIndex×G.ColorIndex) : Foot G× Foot G:=((x,p.1),(y,p.2)); let P(z:Foot G×Foot G):= twin T z.1 z.2 *(hue (lone x a) z.1*hue (lone y b) z.2)
 have hp: Function.support P⊆ Set.range f:=by
    intro z hz
    have hx:z.1.1=x:= Classical.byContradiction fun h=>hz (by unfold P hue lone; rw [if_neg h]; simp)
    have hy:z.2.1=y:= Classical.byContradiction fun h=>hz (by unfold P hue lone; rw [if_neg h]; simp)
    exact ⟨(z.1.2,z.2.2),Prod.ext (Prod.ext hx.symm rfl) (Prod.ext hy.symm rfl)⟩
 rw [← (show Injective f from fun i j h=> Prod.ext (congr_arg (fun p:Foot G×Foot G=>p.1.2) h) (congr_arg (fun p:Foot G×Foot G=>p.2.2) h)).tsum_eq hp]; unfold sparkle; rw [tsum_fintype,Fintype.sum_prod_type]; apply sum_congr rfl;intro i _; apply sum_congr rfl; intro j _; unfold f P hue lone; dsimp only; rw [if_pos rfl,if_pos rfl,mul_comm]
lemma sign_sq (s:Signed)(v:Axis): Pupil.sign s v * Pupil.sign s v=1:=by unfold Pupil.sign; split <;> norm_num
lemma beast_point (p:Signed)(x:Foot G) : beast p (pointA (shore p x)) = sign p x.1.2 • pointA x:=by
 ext1 i; let q:= x.1
 unfold pointA beast;rw [Pi.smul_apply]; unfold shore; by_cases ht:i=q
 · unfold q at ht; subst i; unfold Pupil.sign; split <;> first| simp [lone] -- cases split both
 have hx:i≠ x.1:=ht
 have hh : rotateE p i≠ rotateE p x.1:= fun h=> ht ((revol p).injective h)
 change (if p.flip i.2 then -(lone (rotateE p x.1) _ (rotateE p i)) else _) = _
 unfold lone; dsimp only;rw [if_neg hh,if_neg hx]; simp
lemma shineR (T:Packet (Foot G) 2)(p q:ℝ)(A B:BEdge G) : matchT T ![p • A,q • B]=p*q *matchT T ![A,B]:=by
 rw [pairMatch,pairMatch,← tsum_mul_left]; apply tsum_congr;intro i; unfold hue;simp only [Pi.smul_apply, PiLp.smul_apply,smul_eq_mul];ring
lemma twins_v (T:Packet (Foot G) 2)(p q:Foot G): matchT T ![pointA p,pointA q]=twin T p q:=by
 let P:= (![p,q]:Tuple (Foot G) 2); rw [show ![_,_]= pointA ∘ P from funext fun i => by fin_cases i <;> rfl]; exact authentic ..

def oneS (v:Cover)(x:G.Color) : Cover → G.Color:=fun i=> if i=v then x else 0
lemma single_space (v:Cover)(x:G.Color): (Function.support (oneS v x)).Finite:= (Set.finite_singleton v).subset (fun i hi=> Classical.byContradiction fun h=> hi (by unfold oneS; rw [if_neg (show i≠v from h)]))
lemma point_pay (T:Packet (Foot G) 2)(a:Foot G)(F:BEdge G): matchT T ![pointA a,F]= ∑' t,twin T a t * hue F t :=by
 rw [pairMatch]; let g:(Foot G)×(Foot G)→ℝ:=fun z=>twin T z.1 z.2*(hue (pointA a) z.1*hue F z.2);let f:= Prod.mk a (β:=Foot G)
 have hg: Function.support g⊆Set.range f := by
    intro z (h:g z ≠0); unfold g at h;rw [one_point] at h; split at h
    next he => exact ⟨z.2,Prod.ext he.symm rfl⟩
    next=> simp at h
 rw [← (show Injective f from fun i j h=> congr_arg (Prod.snd :Foot G × Foot G→Foot G) h).tsum_eq hg];apply tsum_congr;intro t; unfold g; rw [one_point,if_pos rfl,one_mul]
lemma asks_r (T:Packet (Foot G) 2)(x:Foot G)(v:Cover)(j:G.ColorIndex) : matchT T ![pointA x,regalia (oneS v (singleR j))] = ∑ i:Axis,(twin T x ((v,i),j)-twin T x ((v-step i,i),j)):=by
 let F:=regalia (oneS v (G:=G) (singleR j))
 rw [point_pay]; let a(i: Axis ⊕ Axis):Foot G:= i.elim (fun i=> ((v,i),j)) (fun i=> ((v-step i,i),j)); let p(t:Foot G):= twin T x t*hue F t
 have hh(i:Axis) : (step i:Cover) ≠0:= by intro h;have hh:= congr_fun h i; simp at hh
 have hm(i:Axis):v-step i≠v:=by intro he; exact hh i (by
                                                           
                                                            exact sub_eq_self.mp he) -- find
 have hr : Function.support p⊆Set.range a:=by
    rintro ⟨⟨q,z⟩,i⟩ hc; change p ((q,z),i)≠0 at hc
    have hx:hue F ((q,z),i)≠0:=fun h=>hc (by unfold p; rw [h,mul_zero])
    unfold F hue regalia oneS at hx; dsimp only at hx; by_cases he:q=v
    · subst q;rw [if_pos rfl,if_neg (by simpa using hh z)] at hx; have hg:i=j:=by by_contra h; simp [singleR,h] at hx
      exact ⟨Sum.inl z,by rw [hg];rfl⟩
    rw [if_neg he] at hx; by_cases hv:q+step z=v
    · rw [if_pos hv] at hx; have hg:i=j:=by by_contra h; simp [singleR,h] at hx
      exact ⟨Sum.inr z,by unfold a; dsimp; rw [hg,← hv,add_sub_cancel_right]⟩
    rw [if_neg hv] at hx;simp at hx
 have hV:Injective a:=by rintro (i|i) (k|k) h <;> have hz:i=k:=congr_arg (fun p:Foot G=>p.1.2) h <;> subst k <;> first|rfl | (exfalso; apply hm i; exact congr_arg (fun p:Foot G=>p.1.1) h.symm) | (exfalso; apply hm i; exact congr_arg (fun p:Foot G=>p.1.1) h)
 change ∑' t,p t= _; rw [← hV.tsum_eq hr,tsum_fintype,Fintype.sum_sum_type]; let g (i:Axis):= p (a (.inr i)); rw [sum_sub_distrib,sub_eq_add_neg]; apply congr_arg₂ (·+·)
 · apply sum_congr rfl;intro i _; simp [p,a,hue,F,regalia,oneS,(hh i),singleR]
 rw [← sum_neg_distrib]; apply sum_congr rfl;intro i _; unfold p a F;dsimp; unfold hue regalia oneS;dsimp only;rw [if_neg (hm i),sub_add_cancel,if_pos rfl];simp [singleR]

lemma allrules (H:W1 U p)(he:e≤p)(hh:G.Simple)(hp:IsSym (U e 2))(h: Throughout (U e 2)): Rules (U e 2):=by
 let T:= U e 2
 refine ⟨?_,h,?_,?_,?_⟩
 · intro i j; let a:= (![j,i]:Tuple (Foot G) 2); change T _=T a; rw [show ![i,j]=a ∘ Equiv.swap 0 1 from funext (fun u=> by fin_cases u <;> (dsimp; rfl))]; exact hp ..
 · intro k x y a b; rw [← rangeT,← rangeT]; let X:= (![lone x a,lone y b]:Fin 2→ BEdge G); have hv i : GivesT (X i):=by fin_cases i <;> exact gives_lone
   rw [show ![lone x (G.adjoint k a), lone y (G.adjoint k b)]=vbadge k ∘ X from funext (fun i=> by fin_cases i <;> exact (lone_h ..).symm)] -- occurrence wrong
   exact (WOne.vbadge_match H he hp X hv (by omega) k).symm
 · intro p x y;let X:= (![pointA (shore p x),pointA (shore p y)]:Fin 2→BEdge G); let a:= sign p x.1.2; let b:= sign p y.1.2; have hv j : GivesT (X j):=by fin_cases j <;> exact gives_lone
   rw [← twins_v,← twins_v _ x y, ← WOne.beast_match H he hp X hv (by omega) p,show beast p ∘ X= ![a • pointA x,b • pointA y] from funext (fun j=>by fin_cases j <;> exact beast_point ..)]; exact shineR ..
 intro x v j
 let A:= (![pointA x,regalia (oneS v (singleR j))]:Fin 2→BEdge G);let hv:=(single_space v (G:=G) (singleR j)); have hc i:GivesT (A i):=by fin_cases i; exact gives_lone; exact gives_reg hv
 rw [← asks_r]; exact WOne.b_pole H he hh _ hv _ hc hp rfl
end YM.RegulatorIR.Pupil
