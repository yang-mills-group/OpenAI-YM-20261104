import YM.WilsonCoeffUV.Step.Interlace
import YM.UVNext.FREE_STRESS_CERTIFICATE.Color
/-! Signed/spatial and color rules on the ordinary bulk torus. Metric from
`Gauge.Color`, not matrix Frobenius. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter Metric
open Blue FreeResolvent Tree Matrix PowerSeries Next.Free Gauge
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
variable {c f : Side}{G:Gauge}
private lemma trace_r {U:Type}[Fintype U]{P:Gen ℝ U}(p:FiniteGen P)(h:Pure P){r}(v:Fin r→U) : tally r v (totalR P)=r.factorial • P r v := by
  let N:=max (r+1) p.choose
  have hr:r<N := Nat.lt_of_lt_of_le (r.lt_add_one) (le_max_left ..)
  rw [visible (p.choose_spec.mono (show p.choose≤N from le_max_right ..)), map_sum];
  rw [Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr hr),Blue.rotate _ (h r)];
  exact fun i _ hi=> pale hi (P i) (h i) v
lemma gen_inj {U:Type}[Fintype U]{P Q:Gen ℝ U}(p:FiniteGen P)(q:FiniteGen Q)(h:Pure P)(e:Pure Q)(hy:totalR P=totalR Q) : P=Q := by
  ext i j; apply (smul_right_inj (M:=ℝ) i.factorial_ne_zero).mp; rw [←trace_r p h,←trace_r q e,hy]

/-- for R taking actual logs LINEAR. -/
lemma surname {P Q:PChart G c}{s b} (h:rollTest (flash P) (flash Q) s b){m n}(p:shellK m P)(q:shellK n Q)
    (hp:∀ i,Pure (P i))(hq:∀ i,Pure (Q i))(R:Matrix (Woods G c) (Woods G c) ℝ)(y:G.El)(e:∀ x : TreeVars G c,
       mantle (R*ᵥ x)= Lattice.gauge (fun _=>y) (pull s b (mantle x))) (i): P i=fade R (Q i) := by
  classical
  have H : TurnsG s b (fun (_:TreeVars G c) _=>y) id (fun x=>R*ᵥ x) := ⟨contDiffAt_id,board R,rfl,Matrix.mulVec_zero _,fun _=> contDiffAt_const,Eventually.of_forall e⟩
  have he:= h H
  have hx: train (spool (id:TreeVars G c→_))= RingHom.id _ := by
    have he j : spool (id:TreeVars G c→_) j=path j := mul_left_cancel₀ (a:=PowerSeries.X) X_ne_zero (by rw [spool_raised id rfl]; exact jet_arg j)
    rw [show spool _=path from funext he,train_id]
  rw [hx,RingHom.id_apply,spool_loom, loom_fade R _ (finite_shell q)] at he
  apply gen_inj (finite_shell p i) (fade_finite (finite_shell q i) R) (hp i) (fade_pure (hq i) R)
  simpa only [flash,coeff_mk] using congr_arg (coeff i) he

-- positive oriented shifts from Lattice hypotheses
def entryS (G:Gauge)(c:Side): Edge (Site c) × G.ColorIndex ≃ Woods G c :=
 { toFun := fun i=> (i.1.1,coord i.1.2,i.2)
   invFun:= fun i=> ((i.1,axisEquiv.symm i.2.1),i.2.2)
   left_inv:= fun i=> by simp [← coord_map]
   right_inv:= fun i=> by simp [← coord_map] }

def toss (G:Gauge)(s:Signed)(t:Site c) : Equiv.Perm (Woods G c) := (entryS G c).symm.trans ((Equiv.prodCongr (Equiv.ofBijective _ ⟨sendEdge_injective s t,Finite.injective_iff_surjective.mp (sendEdge_injective s t)⟩) (Equiv.refl G.ColorIndex)).trans (entryS G c))
lemma toss_at (s:Signed)(t:Site c)(i:Edge (Site c))(j:G.ColorIndex) : toss G s t (entryS G c (i,j))=entryS G c (sendEdge s t i,j) := by rw [toss,Equiv.trans_apply,Equiv.symm_apply_apply]; rfl

-- matrix
def signsT (s:Signed)(w:Woods G c): ℝ:= if s.flip (axisEquiv.symm w.2.1) then -1 else 1
def markSign (G:Gauge)(s:Signed)(b:Site c) : Matrix (Woods G c) (Woods G c) ℝ:= of fun i j=> if j=toss G s b i then signsT s i else 0
lemma sign_on (s:Signed)(b:Site c)(x:TreeVars G c)(i): (markSign G s b *ᵥ x) i=signsT s i*x (toss G s b i) := by unfold mulVec dotProduct markSign; rw [Finset.sum_eq_single (toss G s b i)] <;> simp +contextual

def dyes' (i:Edge (Site c))(x:TreeVars G c) : Lawn G.ColorIndex:= fun j=>x (entryS G c (i,j))
lemma bare_linkC (i:Edge (Site c))(x:TreeVars G c): mantle x i=G.lieExp (coatC G (dyes' i x)):= by unfold mantle; rw [Work.F03.represent_link]; rfl
lemma sign_turn (s:Signed)(b:Site c)(x:TreeVars G c):
    mantle (markSign G s b *ᵥ x) = pull s b (mantle x) := by
  funext a; rcases a with ⟨x',v⟩
  have he : dyes' (x',v) (markSign G s b *ᵥ x)=(if s.flip v then -1 else (1:ℝ)) • dyes' (sendEdge s b (x',v)) x := by
    funext j; unfold dyes'; rw [sign_on, toss_at]; simp only [Pi.smul_apply,smul_eq_mul,signsT];
    rw [show (entryS G c _).2.1=axisEquiv v from rfl, Equiv.symm_apply_apply]
  rw [bare_linkC,he]; unfold pull Step.read; cases hv : s.flip v <;> simp only [Step.rotate,posDir,hv, Bool.false_xor, ↓reduceIte, Bool.false_eq_true]
  · rw [one_smul]; rw [← bare_linkC]; simp [sendEdge,Step.rotate,hv,posDir]
  rw [neg_smul,one_smul,map_neg,Work.F03.exp_neg_color]; rw [←bare_linkC]; simp [sendEdge,Step.rotate,hv,posDir]

lemma signed_pair {P P': PChart G c}{s b} (h:rollTest (flash P) (flash P') s b){m n}(p:shellK m P)(q:shellK n P')(hp:∀ i,Pure (P i))(hq:∀ i,Pure (P' i))(k r :ℕ)(x:Fin r→Woods G c):
    P k r (toss G s b ∘ x) = (∏ i,signsT s (x i)) * P' k r x := by
  rw [surname h p q hp hq (markSign G s b) 1 (fun i=>by rw [sign_turn]; ext1 a; simp [Lattice.gauge]),fade]
  rw [Finset.sum_eq_single x]
  · simp [markSign]
  · intro i _ H; obtain ⟨a, ha⟩:= Function.ne_iff.mp H; rw [Finset.prod_eq_zero (Finset.mem_univ a), zero_smul]; simp [markSign,ha.symm]
  simp

-- adjoint color uniqueness even for individual order, not merely kinetic Hessian

def palette (u:G.El) : G.Color→ₗ[ℝ] G.Color := G.adjoint u
def gammaC (u:G.El) : Matrix G.ColorIndex G.ColorIndex ℝ := LinearMap.toMatrix' ((coatC G).symm.toLinearMap.comp ((G.adjoint u).comp (coatC G).toLinearMap))

def shadeS (u:G.El) (c:Side) : Matrix (Woods G c) (Woods G c) ℝ:= of fun i j=> if ((entryS G c).symm i).1=((entryS G c).symm j).1 then gammaC u i.2.2 j.2.2 else 0
lemma dyes_mat (u:G.El)(v:TreeVars G c)(i) : dyes' i (shadeS u c*ᵥ v)=gammaC u *ᵥ dyes' i v:= by
  funext j; unfold mulVec dotProduct dyes';
  dsimp only
  rw [← Equiv.sum_comp (entryS G c), Fintype.sum_prod_type]; rw [Finset.sum_eq_single i];
  · simp only [shadeS, of_apply,Equiv.symm_apply_apply, ↓reduceIte]; rfl
  · intro x _ h; simp [shadeS,h.symm]
  simp
lemma shade_link (u:G.El)(x:TreeVars G c): mantle (shadeS u c*ᵥ x)=Lattice.gauge (fun _=>u) (mantle x):= by
  funext a; rw [bare_linkC,dyes_mat, Lattice.gauge,bare_linkC];
  rw [gammaC,LinearMap.toMatrix'_mulVec];
  change G.lieExp ((coatC G) ((coatC G).symm _))=_; rw [ContinuousLinearEquiv.apply_symm_apply]; exact Push.Loops.exp_adjoint _ _

-- evaluate fixed-rank tensor against vectors
section
variable (x:Edge (Site c))
def hut (x:Edge (Site c))(G:Gauge) : G.Color→ₗ[ℝ] TreeVars G c:= LinearMap.pi fun i:Woods G c=> if ((entryS G c).symm i).1=x then (LinearMap.proj (R:=ℝ) (φ:=fun _:G.ColorIndex=>ℝ) i.2.2).comp (coatC G).symm.toLinearMap else 0
lemma dyes_hut (a:G.Color)(b:Edge (Site c)): dyes' b (hut x G a)= if b=x then a.ofLp else 0 := by funext i; unfold dyes' hut; rw [LinearMap.pi_apply,Equiv.symm_apply_apply]; split; rfl; rfl
lemma hut_equi (u:G.El)(a:G.Color): hut x G (G.adjoint u a) = shadeS u c*ᵥ hut x G a := by
  funext i; obtain ⟨⟨v,j⟩,rfl⟩:= (entryS G c).surjective i
  change dyes' v (hut x G (G.adjoint u a)) j= dyes' v (shadeS u c*ᵥ hut x G a) j
  rw [dyes_mat,dyes_hut,dyes_hut]; split
  · rw [gammaC,LinearMap.toMatrix'_mulVec]; rfl
  rw [Matrix.mulVec_zero]
lemma unit_hut (a:G.ColorIndex) : hut x G (coatC G (Pi.single a 1))=Pi.single (entryS G c (x,a)) 1 := by
  funext i; obtain ⟨⟨v,j⟩,rfl⟩:= (entryS G c).surjective i
  rw [Pi.single_apply]; change dyes' v _ j= _; rw [dyes_hut]; simp only [(entryS G c).injective.eq_iff]
  split; next h=> change Pi.single (M:=fun _=>ℝ) a 1 j= _; simp [Pi.single_apply,h]
  next h=> simp [h]
end

section
variable {P:PChart G c}
lemma byShade (w:rollTest (flash P) (flash P) 1 0){n : ℕ}(p:shellK n P)(h:∀ i,Pure (P i))(k) (u:G.El) : P k=fade (shadeS u c) (P k):= surname w p p h h _ u (fun x=> by rw [shade_link,Lattice.pull_id]) _

-- matrix rep

def testM (P:PChart G c)(j:ℕ) : Matrix (Woods G c) (Woods G c) ℝ := of fun i u=> P j 2 ![i,u]
lemma test_shade (w:rollTest (flash P) (flash P) 1 0){n : ℕ}(p:shellK n P)(h:∀ i,Pure (P i))(k : ℕ)(u:G.El) : testM P k=(shadeS u c).transpose*testM P k * shadeS u c := by
  ext1 i j
  let M:= shadeS u c
  change P k 2 _=_; conv_lhs => rw [byShade w p h k u]
  unfold fade
  -- reindex
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 2=> Woods G c)), Fintype.sum_prod_type];
  simp_rw [Matrix.mul_apply,Finset.sum_mul]; conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _:Fin 1=> Woods G c)),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro y _; rw [Fintype.sum_unique];
  let Q: Fin 2→Woods G c:= Fin.cons x (Fin.cons y (fun i=>i.elim0))
  simp only [Fin.consEquiv_apply,Fin.prod_univ_two,Fin.cons_zero,Fin.cons_one]
  simp only [transpose_apply,testM,Matrix.of_apply];
  have he (t:Fin 0→Woods G c): Fin.cons x (Fin.cons y t)=![x,y]:= funext fun i=> by fin_cases i <;> simp
  change M x i*M y j*P k 2 (Fin.cons x (Fin.cons y (default:(Fin 0 → Woods G c))))= M x i * P k 2 ![x,y]*M y j
  rw [he]; ring

-- bilinear form restricted to two physical bonds

def evaluateTwo (K:Matrix (Woods G c) (Woods G c) ℝ)(x y : Edge (Site c)) : G.Color →ₗ[ℝ] G.Color→ₗ[ℝ]ℝ where
  toFun i:={
    toFun j:= dotProduct (hut x G i) (K*ᵥ hut y G j)
    map_add' a b:= by simp only [map_add,mulVec_add,dotProduct_add]
    map_smul' a b:= by simp only [map_smul,mulVec_smul, dotProduct_smul]; rfl }
  map_add' a b:= by ext w; change dotProduct (hut x G _) _= _; rw [map_add,add_dotProduct]; rfl
  map_smul' a b:= by ext w; change dotProduct (hut x G _) _=_; rw [map_smul, smul_dotProduct]; rfl

lemma two_shade (hs:G.Simple)(w:rollTest (flash P) (flash P) 1 0){n:ℕ}(h:shellK n P)(p:∀ i,Pure (P i))(e:ℕ)(x y:Edge (Site c)):
    ∃ k:ℝ, ∀ i j:G.ColorIndex,P e 2 ![entryS G c (x,i),entryS G c (y,j)]= if i=j then k else 0:= by
  let M:=testM P e; let T:=evaluateTwo M x y
  have he (u:G.El) (a b:G.Color): T (G.adjoint u a) (G.adjoint u b)=T a b:= by
    let S:=shadeS u c
    change dotProduct _ _ = dotProduct _ _
    conv_rhs=>rw [show M=S.transpose*M*S from test_shade w h p e u]
    rw [hut_equi,hut_equi,← Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,dotProduct_transpose_mulVec]; apply dotProduct_comm
  obtain ⟨r,H⟩:= UVNext.FreeStress.real_color_form hs T he
  refine ⟨r,fun i j=>?_⟩
  have hu:= H (coatC G (Pi.single i 1)) (coatC G (Pi.single j 1));
  change dotProduct (hut _ _ _) (M*ᵥ hut _ _ _) = _ at hu
  rw [unit_hut,unit_hut,single_one_dotProduct, mulVec_single_one,← color_dot] at hu
  change P e 2 _=r*dotProduct (Pi.single (M:=fun _=>ℝ) i 1) (Pi.single (M:=fun _=>ℝ) j 1) at hu
  rw [hu]; by_cases hh:i=j<;>simp [hh]

def spinOne (K:TreeVars G c)(x:Edge (Site c)): G.Color →ₗ[ℝ]ℝ where
    toFun i:= dotProduct K (hut x G i)
    map_add' a b:= by rw [map_add,dotProduct_add]
    map_smul' a b:= by simp only [map_smul, dotProduct_smul]; rfl
lemma no_beam (hs:G.Simple)(w:rollTest (flash P) (flash P) 1 0){n:ℕ}(h:shellK n P)(p:∀ i,Pure (P i))(e): P e 1=0 := by
  let K i:=P e 1 ![i]; have hm u: K=(shadeS u c).transpose*ᵥ K:= by
    funext i; change P e 1 _= _; conv_lhs=> rw [byShade w h p e u]
    rw [fade,←Equiv.sum_comp (Fin.consEquiv (fun _:Fin 1=> Woods G c)),Fintype.sum_prod_type];
    apply Finset.sum_congr rfl; intro y _; rw [Fintype.sum_unique];
    simp only [Fin.consEquiv_apply,Fin.prod_univ_one, Fin.cons_zero,smul_eq_mul]
    congr 1
  have he (x): spinOne K x=0:=UVNext.FreeStress.no_linear hs _ fun u v=>by
    change dotProduct K _ = dotProduct K _; rw [hut_equi];
    conv_rhs=>rw [hm u];
    rw [dotProduct_mulVec, Matrix.mulVec_transpose]
  ext1 i
  have hv := (entryS G c).surjective (i 0); obtain ⟨⟨x,j⟩,hj⟩:=hv
  have hh: (spinOne K x) (coatC G (Pi.single j 1))=0:= by rw [he];rfl
  unfold spinOne at hh; change dotProduct K (hut _ _ _)=_ at hh
  rw [unit_hut,dotProduct_single_one] at hh
  change P e 1 ![_]=_ at hh
  rwa [show ![entryS G c (x,j)]=i from funext fun i'=> by fin_cases i'; simpa] at hh

end
end YM.WilsonCoeffUV.Power
