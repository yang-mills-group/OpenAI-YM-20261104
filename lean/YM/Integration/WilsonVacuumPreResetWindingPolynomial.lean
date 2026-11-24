import YM.Integration.WilsonVacuumPreResetAngularDifference

/-! At fixed coupling degree the entire finite connected Wilson step is a
polynomial of bounded degree in an interpolation of the incoming vacuum.
The Schur form, affine field, Haar series and kinetic subtraction stay fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetWindingPolynomial
open Function Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open scoped BigOperators Classical

def At (d:ℕ)(f:ℝ→ℝ):Prop:=∃p:Polynomial ℝ,p.natDegree ≤ d ∧ ∀t,p.eval t=f t

theorem constant (d:ℕ)(c:ℝ):At d (fun _=>c):=
  ⟨Polynomial.C c,by simp,fun t=>by simp⟩

theorem add {d:ℕ}{f g:ℝ→ℝ}(hf:At d f)(hg:At d g):At d (fun t=>f t+g t):=by
  obtain ⟨P,hP,vP⟩:=hf
  obtain ⟨Q,hQ,vQ⟩:=hg
  exact ⟨P+Q,(Polynomial.natDegree_add_le ..).trans (max_le hP hQ),fun t=>by simp [vP t,vQ t]⟩

theorem sub {d:ℕ}{f g:ℝ→ℝ}(hf:At d f)(hg:At d g):At d (fun t=>f t-g t):=by
  obtain ⟨P,hP,vP⟩:=hf
  obtain ⟨Q,hQ,vQ⟩:=hg
  exact ⟨P-Q,(Polynomial.natDegree_sub_le ..).trans (max_le hP hQ),fun t=>by simp [vP t,vQ t]⟩

theorem mul {d e:ℕ}{f g:ℝ→ℝ}(hf:At d f)(hg:At e g):At (d+e) (fun t=>f t*g t):=by
  obtain ⟨P,hP,vP⟩:=hf
  obtain ⟨Q,hQ,vQ⟩:=hg
  exact ⟨P*Q,(Polynomial.natDegree_mul_le ..).trans (Nat.add_le_add hP hQ),fun t=>by simp [vP t,vQ t]⟩

theorem scale {d:ℕ}{f:ℝ→ℝ}(c:ℝ)(h:At d f):At d (fun t=>c*f t):=by
  simpa only [Nat.zero_add] using mul (constant 0 c) h

theorem sums {ι:Type*}{d:ℕ}(s:Finset ι)(f:ι→ℝ→ℝ)(h:∀i∈s,At d (f i)):
    At d (fun t=>∑i∈s,f i t):=by
  induction s using Finset.induction_on with
  | empty=>simpa using constant d 0
  | insert i S hi ih=>
    simpa only [Finset.sum_insert hi] using add (h i (mem_insert_self ..))
      (ih fun j hj=>h j (mem_insert_of_mem hj))

theorem affine {d:ℕ}(pos:0<d)(a c:ℝ):At d (fun t=>a+t*c):=by
  refine add (constant d a) (⟨Polynomial.X*Polynomial.C c,?_,fun _=>by simp only [Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]⟩:At d (fun t=>t*c))
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_X,Polynomial.natDegree_C,Nat.add_zero]
  omega

variable {U V:Type} [Fintype U]
def Entries (d:ℕ)(f:ℝ→Gen ℝ U):Prop:=∀r x,At d (fun t=>f t r x)

omit [Fintype U] in
private theorem severed {k:ℕ}{p:ℝ→Gen ℝ U}(h:Entries k p)(a:U):
    Entries k (fun t=>sever a (p t)):=by
  intro r x
  simp only [sever,prune,Pi.smul_apply,nsmul_eq_mul]
  exact scale _ (h _ _)

omit [Fintype U] in
private theorem spored {k e:ℕ}{p q:ℝ→Gen ℝ U}(h:Entries k p)(v:Entries e q):
    Entries (k+e) (fun t=>spore (p t) (q t)):=by
  intro r x
  simp only [spore,Finset.sum_apply]
  apply sums
  intro j hj
  have hj' : j.1+j.2=r:=by simpa using hj
  simp only [interweave,dif_pos hj',smul_eq_mul]
  exact mul (h _ _) (v _ _)

omit [Fintype U] in
theorem swirled {k r:ℕ}{p:ℝ→Ten ℝ U r}(h:∀x,At k (fun t=>p t x))(x:Fin r→U):
    At k (fun t=>swirl (p t) x):=by
  simp only [swirl,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  apply scale
  exact sums _ _ fun _ _=>h _

private theorem rippled (K:Matrix U U ℝ){k:ℕ}{p:ℝ→Gen ℝ U}(h:Entries k p):
    Entries k (fun t=>ripple K (p t)):=by
  intro r x
  simp only [ripple,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sums
  intro a _
  apply sums
  intro b _
  exact scale _ (severed (severed h _) _ r x)

private theorem joined (K:Matrix U U ℝ){k e:ℕ}{p q:ℝ→Gen ℝ U}(h:Entries k p)(v:Entries e q):
    Entries (k+e) (fun t=>arbor K (p t) (q t)):=by
  intro r x
  simp only [arbor_form,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sums
  intro a _
  apply sums
  intro b _
  exact scale _ (swirled (spored (severed h a) (severed v b) r) x)

private theorem connected (K:Matrix U U ℝ)(p:ℝ→ℕ→Gen ℝ U)(start:∀e,Entries e (fun t=>p t e)):
    ∀h e,Entries e (fun t=>abr K (p t) h e):=by
  intro h
  induction h using Nat.strong_induction_on with
  | h n ih=>
    intro e r x
    cases n with
    | zero=>simpa only [abr] using start e r x
    | succ k=>
      simp only [abr_next,Pi.smul_apply,Pi.add_apply,smul_eq_mul,ravel,Finset.sum_apply]
      apply scale
      apply add
      · exact rippled K (ih k (by omega) e) r x
      · apply sums
        intro i hi
        apply sums
        intro j hj
        have hsum:i.1+i.2=k:=by simpa using hi
        have je:j.1+j.2=e:=by simpa using hj
        exact je ▸ joined K (ih i.1 (by omega) j.1)
          (ih i.2 (by omega) j.2) r x

theorem folded {I:Type}[Fintype I] (K:Matrix U I ℝ){e:ℕ}{p:ℝ→Gen ℝ U}
    (h:Entries e p):Entries e (fun t=>fade K (p t)):=by
  intro r x
  simp only [fade,smul_eq_mul]
  exact sums _ _ fun _ _=>scale _ (h _ _)

variable {G:Gauge} {c f:Side}

private theorem quiet (S:StepData c f)(F:Forest S.ratio)(H:FreeResolvent.FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P D:PChart G f):
    ∀h i,Entries i (fun t=>xray S F H Q O (P+t•D) h i):=by
  let M:=extractV G S F Q
  let A:=fun t:ℝ=>casePW S O M (P+t•D)
  have passed (i:ℕ):Entries i (fun t=>scrub (P+t•D) i):=by
    intro j y
    by_cases zero:i=0
    · simp only [scrub,zero,↓reduceIte,Pi.zero_apply];exact constant _ 0
    · simp only [scrub,if_neg zero,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      exact affine (Nat.pos_of_ne_zero zero) _ _
  have primitives (i:ℕ):Entries i (fun t=>A t i):=by
    intro j y
    change At i (fun t=>_ - fade (camber G M) (scrub (P+t•D) i) j y)
    exact sub (constant _ _) (folded (camber G M) (passed i) j y)
  exact connected _ A primitives

/-- All forest, tag, noise, Haar and mixed inherited terms of the actual
finite-period unmarked update are retained before extracting one angular row. -/
theorem original (S:StepData c f)(F:Forest S.ratio)(H Y:FreeResolvent.FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P D:PChart G f)
    (e r:ℕ)(x:Fin r→Woods G c):
    At e (fun t=>winter S F H Y Q O (P+t•D) e r x):=by
  unfold winter
  simp only [Pi.add_apply,Pi.sub_apply]
  apply add _ (constant _ _)
  apply sub (constant _ _)
  apply folded
  intro j y
  simp only [Finset.sum_apply]
  exact sums _ _ fun h _=>quiet S F H Q O P D h e j y

private theorem marked_heat (K:Matrix U U ℝ)(fields:ℝ→Layers ℝ U)(T:ℝ→Pal ℝ U)(d:ℕ)
    (cost:∀h e,Entries e (fun t=>fields t h e))(paid:∀e,Entries (e+d) (fun t=>T t e)):
    ∀h e,Entries (e+d) (fun t=>bul K (fields t) (T t) h e):=by
  intro h
  induction h using Nat.strong_induction_on with
  | h n ih=>
    intro e r x
    cases n with
    | zero=>simpa only [bul_zero] using paid e r x
    | succ k=>
      have drift (C:Matrix U U ℝ):At (e+d)
          (fun t=>ravel C (fields t) (bul K (fields t) (T t)) k e r x):=by
        simp only [ravel,Finset.sum_apply]
        apply sums
        intro a ha
        apply sums
        intro b hb
        have date:a.1+a.2=k:=by simpa using ha
        have degree:b.1+b.2=e:=by simpa using hb
        have fee:b.1+(b.2+d)=e+d:=by omega
        exact fee ▸ joined C (cost a.1 b.1) (ih a.2 (by omega) b.2) r x
      simp only [bul_next,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
      exact scale _ (add (add (rippled K (ih k (by omega) e) r x) (drift K)) (drift K.transpose))

/-- The genuine joint Gaussian heat coefficient when the marked input
also depends on the interpolation parameter. -/
theorem companion (S:StepData c f)(F:Forest S.ratio)(H:FreeResolvent.FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P D:PChart G f)
    (T:ℝ→PChart G f)(d:ℕ)(paid:∀e,Entries (e+d) (fun t=>T t e)):
    ∀h e,Entries (e+d) (fun t=>srShade S F H Q O (P+t•D) (T t) h e):=by
  let M:=extractV G S F Q
  let K:=fillSlots (Woods G c) (FreeResolvent.covariance G S F H)
  apply marked_heat K (fun t=>xray S F H Q O (P+t•D)) (fun t=>srCold (T t) M) d
    (quiet S F H Q O P D)
  intro e
  exact folded (camber G M) (paid e)

/-- The normalized occupied response to a signed interpolation of the
entire old quiet inlet. Each occurrence of its perturbation costs a
positive coupling grade. This includes the occupied angular scalar. -/
theorem occupied (S:StepData c f)(F:Forest S.ratio)(H:FreeResolvent.FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P D T:PChart G f)
    (l e r:ℕ)(x:Fin r→Woods G c):
    At e (fun t=>reed S F H Q O (P+t•D) l T e r x):=by
  have billed:=companion S F H Q O P D (fun _=>T) 0 (fun e r x=>constant e (T e r x))
  unfold reed
  apply folded
  intro i y
  simp only [Finset.sum_apply]
  exact sums _ _ fun h _=>billed h e i y

end YM.Integration.WilsonVacuumPreResetWindingPolynomial
end

