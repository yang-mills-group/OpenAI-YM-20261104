import YM.X.Reed.Starf
/-!
# Applied probes of canonical jets. (Including longitudinal lattice sectors for FO Ward). Works at any polynomial horizon including empty geometry.)
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Wilson Stems Next.Rank.CellsInt Next.Rank.Beamer Next.Rank.Configuration Tensor TensorProduct Filter MeasureTheory Metric Finset Function Maxwell Labels Asymptotics
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n k m d:ℕ} {A:Brush G} {W:Type*}
def advert : Brush G→ₗ[ℝ] Horizon G:= LinearMap.pi fun i:Address G=> (EuclideanSpace.proj i.2.2).toLinearMap ∘ₗ (LinearMap.proj i.1) ∘ₗ curlL i.2.1.val.1 i.2.1.val.2
lemma ad(a:Brush G): polar (advert a)= fun i j=> curlL i j a:= by
   have ht i j: curlL i j a = -curlL j i a:= (trot_secure a).ax .. -- ..!
   have he(x:Cover)(i j:Axis)(h:i<j) : polar (advert a) i j x= curlL i j a x:= PiLp.ext fun l=> poll_at (advert a) _ _ x h l
   funext i j z; rcases lt_trichotomy i j with h|h|h
   · exact he z i j h
   · subst i; change _ = stepValue (raising j _) j _-stepValue (raising j _) j _; rw [polar]; simp
   rw [Next.Rank.Beamer.reverse,ht i j, Pi.neg_apply,Pi.neg_apply, he _ _ _ h]
lemma advertisements (x:Brush G) : shutter (advert x):= by intro a b c; rw [ad]; exact (trot_secure x).holds ..
lemma by_pass {f:Cover→G.Color}: advert (raised f)=0:= by
   have he i j : curlL i j (raised f) =0:= by change stepValue (stepValue f j) i-stepValue (stepValue f i) j=0; rw [hop,sub_self];
   ext1 x; change curlL _ _ _ _ _=0; rw [he];rfl
lemma vanish_ad (L:Degree G) (h:n≤ L.degree+1)(p:Cloudless n A): gesture L (advert A)=0:= by
   rw [gesture_hits,ad]; let i:= L.a.val.1; let j:=L.a.val.2
   change jumps L.degree L.layout (stepValue (raising j _) i-stepValue (raising i _) j:Cover→G.Color) L.point _=0; rw [jumps_sub]; change (jumps _ _ (stepValue (raising j A) i) _ _ - jumps _ _ (stepValue (raising i A) j) _ _)=0; rw [← steps,← steps]
   have hp (l:Fin (L.degree+1)→Axis)(j:Axis) : jumps _ l (raising j A) =0:= cloud_rise p h l j
   rw [hp,hp,sub_self]
lemma in_nil (p:KeyIn G d)(h:n< Labels.generation p.val) (hp:Cloudless n A): predicts p (advert A)=0:=by
   rw [concentrates]; refine sum_eq_zero fun i _=>?_ ; rw [vanish_ad _ _ hp,zero_mul]; have he:= i.property; unfold generation at h;omega
lemma out_nil (p: Address G)(hp:Cloudless d A) : foam d p (advert A)=0:= by
   let Q:= advert A; rw [foams]; let y:=Q-cloud d Q
   suffices h: ∀L:Degree G,L.degree=d-1→gesture L y=0 by
      have he:=advertisements A
      apply norm_le_zero_iff.mp; refine le_trans (retreat (d:=d) y (by unfold y; rw [map_sub,visible d Q he,sub_self]) 0 le_rfl (street p.1) (fun L hL _=> (by rw [h L hL,norm_zero])) p le_rfl) (by rw [mul_zero]); -- potential y macro rw error
   intro L h; change gesture L (_-_) =0; rw [map_sub,absent h,vanish_ad _ (by omega) hp,sub_self] -- let syntax

def signal_arc (x:Address G): Fan G:= Stems.arc x.2.2 x.1 x.2.1.val.1 x.2.1.val.2
lemma arc_flat (x: Address G): flatL A (signal_arc x)=advert A x:= by rw [flatL,signal_arc,arc_eq,←curling]; rfl
abbrev Horizontal(G:Gauge): Submodule ℝ (Fan G):= Submodule.span ℝ (Set.range signal_arc)
lemma horn {x:Fan G}(h:x∈Horizontal G) (f:Cover→G.Color): taste x (raised f)=0:= by
   rw [taste_eval]; exact (show Horizontal G ≤ LinearMap.ker (flatL (raised f)) from Submodule.span_le.mpr (by rintro _ ⟨p,rfl⟩; rw [SetLike.mem_coe,LinearMap.mem_ker,arc_flat,by_pass];rfl)) h -- name
variable (f:W→Address G)
private abbrev B(d:ℕ)(w:KeyIn G d ⊕ W): Address G→₀ℝ:= (bright_pass f 1 d w).choose
def optic (d:ℕ)(i:KeyIn G d⊕W):Fan G:= Finsupp.linearCombination ℝ signal_arc (B f d i)
lemma sees (d:ℕ)(i:KeyIn G d⊕W)(x: Brush G) : flatL x (optic f d i) = passcode f 1 d i (advert x):= by
    rw [(bright_pass f 1 d i).choose_spec,optic,LinearMap.map_finsupp_linearCombination]; apply DFunLike.congr_fun; apply congr_arg; exact funext (fun _=> arc_flat _) -- inspect
lemma omen (d:ℕ)(i:KeyIn G d⊕W) : optic f d i∈ Horizontal G:= by unfold optic Horizontal; let t:= B f d i; change (∑ j∈t.support,t j • signal_arc j)∈ Horizontal G; apply Submodule.sum_mem;intro j hj;exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
lemma occ (d:ℕ)(i: KeyIn G d⊕W): optic f d i∈grads G ((bear i)-1):= by
    refine (cloud_ann _).mpr (fun s h=>?_); rcases i with i|j
    · rw [sees,item,in_nil i _ h,mul_zero]; change Labels.generation i.val-1<Labels.generation i.val; unfold generation; omega
    rw [sees]; change _ * foam d _ _=0; rw [out_nil _ _,mul_zero]; simpa only [bear,Sum.elim_inr,Nat.add_sub_cancel] using h

lemma arc_occ (x:Address G): signal_arc x∈ grads G 1:= by apply (cloud_ann _).mpr; intro A H; rw [arc_flat]; exact vanish_ad (L:=⟨x.2.1,x.2.2,x.1,0,Fin.elim0⟩) (by simp) H

-- ∗Leading charge∗ degree match for probes. compare predictors on all ghost hub data.
lemma proj (L:KeyIn G d)(h:L.val.1=n)(p:Specs G (n+1)) :
     let T:= contracted (trot_closed p); predicts L (advert (port _ p)) = predicts L (sweep n T):= by
     intro T; rw [concentrates,concentrates]; refine sum_congr rfl fun j _=>?_ ; apply congr_arg (· * _); let a := j.val.a.val.1; let b:=j.val.a.val.2
     rcases lt_or_eq_of_le j.property.2.1 with hk|hk
     · rw [gesture_over j.val (h ▸ hk)]; rw [vanish_ad _ (n:=n+2) _ (fun l j => larger p j (by omega) l)]; omega
     obtain ⟨⟨v,i,x,k,t⟩,hw⟩:= j; change L.val.1=k at hk; have he:k=n:= hk.symm.trans h; clear hk; subst k;
     let l : Degree G:= ⟨v,i,x,n,t⟩; rw [gesture_hits l,gesture_hits l]; rw [ad, show sweep n T=inspect T from rfl,inspected]; change jumps n t (curlL a b (skew _ p.val)) x i=jumps n t (test T a b) x i; rw [trot_achieves p, top (trot_sym p a b), test_top, show takeCurl T=trot p.val from curl_inverse _]
lemma pred_key (i: Fin (Labels.dim G n))(h:n+2≤d)(T: Labels.Taylor G n) : predicts (⟨⟨n,i⟩,h⟩:KeyIn G d) (sweep n T)= (Labels.axes G n).repr T i:= by
    let f (p : Fin (Labels.dim G n)):KeyIn G d:= ⟨⟨n,p⟩,h⟩; conv_lhs=> enter [2]; rw [← (Labels.axes G n).sum_repr T];
    simp only [map_sum,map_smul];
    have he j : sweep n (axes G n j)=tester (f j).val:= rfl
    simp_rw [he]; change ∑ j: Fin (Labels.dim G n), (axes G n).repr T j • predicts (f i) _ = _; simp_rw [forecast]; rw [sum_eq_single i]; simp; intro j _ hj; have h:f i ≠ f j:= fun hv=> hj (Eq.symm (eq_of_heq (Sigma.mk.inj (congr_arg (fun p:KeyIn G d=>p.val) hv)).2)); rw [if_neg h,smul_zero]; simp
lemma owed (i:Fin (Labels.dim G n))(h:n+2≤d)(p:Specs G (n+1)): flatL (port _ p) (optic f d (.inl ⟨⟨n,i⟩,h⟩))= (Labels.axes G n).repr (contracted (trot_closed p)) i:= by rw [sees,item,proj (n:=n) _ rfl,pred_key,one_pow,one_mul]
end YM.PositionX.Reed
