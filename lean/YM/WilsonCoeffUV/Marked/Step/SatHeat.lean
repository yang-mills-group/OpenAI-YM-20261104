import YM.WilsonCoeffUV.Marked.Step.SourceLaw
/-!
# Closure on address-banach tensor tests

Station product `joy` in logs, disjoint marker. Auth retained.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent
open Filter Cosmos
open scoped Topology BigOperators
variable {ι:Type}{U:Type}{J K S T:Finset ι}{D:ι→ℕ}{i j e r h:ℕ}{G:Gauge}

section
variable [DecidableEq ι](h:J⊆S)
private def vCn (x: Pen D J) (y: Pen D (S\J)):=joy h x y
lemma vJoins : ∃ L: Pen D J→L[ℝ] Pen D (S\J) →L[ℝ] Pen D S,∀ x y,L x y=vCn h x y:=by
   let V:= Pen D J; let W:=Pen D (S\J); let T:=Pen D S
   let f (x:V): W→ₗ[ℝ] T:= {
        toFun y:= joy h x y
        map_add' a b:= by apply pen_inj; intro A; rw [joy_p,map_add,map_add,joy_p,joy_p,mul_add]
        map_smul' c a:= by apply pen_inj; intro A; change touch _ _ (joy h x (c • a))= touch _ _ (c • joy h x a); rw [joy_p,map_smul,map_smul,joy_p]; ring }
   let L: V →ₗ[ℝ] W→ₗ[ℝ]T:= {
       toFun:=f
       map_add' a b:= LinearMap.ext fun x=>pen_inj _ _ fun A=>by change touch _ _ (joy h (a+b) x)=touch _ _ (joy h a x+joy h b x); rw [joy_p,map_add,map_add,joy_p,joy_p,add_mul]
       map_smul' c a:= LinearMap.ext fun x=>pen_inj _ _ fun A=>by change touch _ _ (joy h (c • a) x)=touch _ _ (c • joy h a x); rw [joy_p,map_smul,map_smul,joy_p]; simp [mul_assoc] }
   refine ⟨L.mkContinuous₂ 1 (fun x y=>by rw [one_mul]; exact joy_norm h x y),fun _ _=>rfl⟩
def joinL (D:ι→ℕ): Pen D J→L[ℝ] Pen D (S\J) →L[ℝ] Pen D S:= (vJoins (D:=D) h).choose
lemma waveJoy (x:Pen D J)(y): joinL h D x y=joy h x y:= (vJoins h).choose_spec ..
-- pencil weave (vectors not commRing internally)
def cobT (P:Ten (Pen D J) U i)(Q: Ten (Pen D (S\J)) U j)(r:ℕ) : Ten (Pen D S) U r:=fun x=>if e:i+j=r then joinL h D (P (x ∘ Fin.cast e ∘ Fin.castAdd j)) (Q (x∘ Fin.cast e ∘ Fin.natAdd i)) else 0
def cob (P: Gen (Pen D J) U)(Q: Gen (Pen D (S\J)) U) (r:ℕ) : Ten (Pen D S) U r:=swirl (∑ j∈Finset.antidiagonal r,cobT h (P j.1) (Q j.2) r)
def foam (P:Pal (Pen D J) U)(Q:Pal (Pen D (S\J)) U):Pal (Pen D S) U:=fun e=>∑ j∈ Finset.antidiagonal e,cob h (P j.1) (Q j.2)
def foamT (P:Layers (Pen D J) U)(Q:Layers (Pen D (S\J)) U) :Layers (Pen D S) U:=fun j=>∑ t∈Finset.antidiagonal j,foam h (P t.1) (Q t.2)
abbrev pPly (A:Case D)(S:Finset ι) : Pal (Pen D S) U →ₗ[ℝ] Pal ℝ U:= ply (touch A S).toLinearMap
lemma fp (P:Pal (Pen D J) U)(Q:Pal (Pen D (S\J)) U)(A:Case D) : pPly A S (foam h P Q)=woad (pPly A J P) (pPly A (S\J) Q):=by
    funext i j; change tinct (touch A S).toLinearMap ((foam h P Q) i j) = _; unfold foam woad; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; refine Finset.sum_congr rfl fun k _=>?_ ; unfold cob knitS; rw [cloak_swirl,map_sum]; congr 1; apply Finset.sum_congr rfl; intro l hl; funext x; have ht:= Finset.mem_antidiagonal.mp hl
    change touch _ _ (cobT _ _ _ _ _)=_; rw [cobT,dif_pos ht,waveJoy, joy_p, webT,dif_pos ht]; rfl
lemma fpT (P:Layers (Pen D J) U)(Q:Layers (Pen D (S\J)) U)(A:Case D) :
    (fun i=>pPly A S (foamT h P Q i))= tassel (fun i=> pPly A J (P i)) (fun i=> pPly A (S\J) (Q i)):=funext fun i=>by simp_rw [foamT,map_sum,fp,tassel]

lemma foam_shell (P:Pal (Pen D J) U)(Q:Pal (Pen D (S\J)) U)(p:shellK i P)(q:shellK j Q): shellK (i+j) (foam h P Q):=by
    let Z:=foam h P Q; intro e r t; funext x; apply pen_inj; intro A; change pPly A S Z e r x= touch _ _ 0; rw [map_zero]; have hv:= fp h P Q A; rw [hv]; rw [woad_shell _ _ (ply_shell _ p) (ply_shell _ q) e r t]; rfl
lemma foam_pure (P:Pal (Pen D J) U)(Q:Pal (Pen D (S\J)) U)(i): Pure (foam h P Q i):=by intro v; rw [foam, Finset.sum_apply]; apply Blue.Smooth.sum; exact fun j _=>swirl_smooth _
lemma foamT_stop (P:Layers (Pen D J) U)(Q:Layers (Pen D (S\J)) U)(p:stops i P)(q:stops j Q): stops (i+j) (foamT h P Q):=by
    intro e r t u; funext x; apply pen_inj; intro A
    let X i:= pPly A J (P i); let Y i:=pPly A (S\J) (Q i); have hp: stops i X := fun a b c h=>funext fun x=>by change touch _ _ (P a b c x)=0; rw [p a b c h]; exact map_zero _
    have ht: stops j Y := fun a b c h=>funext fun x=>by change touch _ _ (Q a b c x)=0; rw [q a b c h]; exact map_zero _
    rw [Pi.zero_apply,map_zero]; change pPly A S (foamT h P Q e) _ _ _=0; rw [congr_fun (fpT h P Q A) e,tassel_stop X Y hp ht _ _ _ u]; rfl
lemma foamT_pure (P:Layers (Pen D J) U)(Q:Layers (Pen D (S\J)) U)(j e): Pure (foamT h P Q j e):=by intro v; rw [foamT,Finset.sum_apply,Finset.sum_apply]; apply Blue.Smooth.sum; exact fun i _=>foam_pure _ _ _ _ _

lemma cobBends {P:raw U (Pen D J) i}{Q:raw U (Pen D (S\J)) j}{X:Ten (Pen D J) (Cover×U) i}{Y:Ten (Pen D (S\J)) (Cover×U) j}{o}(b:i+j=r)(t:Bends o P X)(u:Bends o Q Y) : Bends o (fun n=> cobT h (P n) (Q n) r) (cobT h X Y r):= by
   subst r; obtain ⟨s,a,hS,K⟩:=t.price; obtain ⟨v,B,hv,H⟩:=u.price; let m:=min s v; have hm:0≤m:= (lt_min hS hv).le; refine ⟨fun x=>?_,min s v,a*B,lt_min hS hv,(K.and H).mono fun n hn=>?_⟩
   · unfold cobT; simp only [↓reduceDIte]
     let f (v:Pen D J×Pen D (S\J)):= joinL h D v.1 v.2; have hp: Continuous f:= ((joinL h D).continuous.comp continuous_fst).clm_apply continuous_snd
     exact hp.continuousAt.tendsto.comp ((t.point _).prodMk_nhds (u.point _))
   have hx:= hn.1.mono (min_le_left s v); have hy:= hn.2.mono (min_le_right s v); refine ⟨mul_nonneg hx.1 hy.1,fun x=>?_⟩
   unfold cobT; rw [dif_pos rfl, waveJoy]; apply (joy_norm ..).trans; set p:Fin i→_ := x ∘ _ ∘ Fin.castAdd j; set q:Fin j→_:=x ∘ _ ∘ Fin.natAdd i
   have hA:=hx.2 p; have hB:=hy.2 q; refine (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA)).trans ?_; rw [mul_mul_mul_comm,←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg hx.1 hy.1); apply Real.exp_le_exp.mpr; rw [←mul_add,← Nat.cast_add]; exact mul_le_mul_of_nonpos_left (by exact_mod_cast webT_tread _ _ rfl x) (neg_nonpos.mpr hm)

omit h [DecidableEq ι] in
lemma swayB {V: Type}[NormedAddCommGroup V][NormedSpace ℝ V] {P:raw U V i}{T:Ten V (Cover×U) i}(t:Bends 0 P T): Bends 0 (fun n=>swirl (P n)) (swirl T):=by
   have he (j:Equiv.Perm (Fin i)): Bends 0 (fun n x=>P n (x ∘ j)) (fun x=>T (x ∘ j)):=by
       obtain ⟨s,A,h,H⟩:=t.price; refine ⟨fun i=>t.point _,s,A,h,H.mono fun n hn=>⟨hn.1,fun x=>?_⟩⟩; let p:=wrap n (0:Cover); let Q:= ((finSuccEquiv i).trans (Equiv.optionCongr j)).trans (finSuccEquiv i).symm
       have hm: stud p (x ∘ j)= stud p x ∘ Q:= by
          funext i; refine Fin.cases (by simp [Q,stud]) (fun i=> by simp [Q,stud]) i
       apply (hn.2 (x ∘ j)).trans; unfold p at hm; unfold tread; rw [hm,league_equiv]
   let Z:= (Equiv.Perm (Fin i)); let S:Finset Z:=Finset.univ
   exact Soil.Bends.μ (anzas S (fun i _=> he i)) _
lemma crest_foam {P:(n:Side)→Pal (Pen D J) (Site n × U)}{Q:(n:Side)→Pal (Pen D (S\J)) (Site n × U)}{X: Pal (Pen D J) (Cloth U)}{Y: Pal (Pen D (S\J)) (Cloth U)}(p:∀ i r,Bends 0 (fun n:Side=>P n i r) (X i r))(q:∀ i r,Bends 0 (fun n:Side=> Q n i r) (Y i r))(e r): Bends 0 (fun n=> foam h (P n) (Q n) e r) (foam h X Y e r):=by
   simp_rw [foam,Finset.sum_apply]; apply anzas (P:=fun (j:ℕ×ℕ) n=> cob h (P n j.1) (Q n j.2) r); intro i _; apply swayB
   exact anzas (P:=fun (j:ℕ×ℕ) n=> cobT h (P n i.1 j.1) (Q n i.2 j.2) r) (Finset.antidiagonal r) (fun j hj=>cobBends h (Finset.mem_antidiagonal.mp hj) (p i.1 j.1) (q i.2 j.2))
end
end YM.WilsonCoeffUV.Wheel.Mark
