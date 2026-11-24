import YM.WilsonCoeffUV.Reclosure.Paths.WindingAlias
/-!
# Signed channel of normalized Taylor coefficients

On cover Sig acts on potentials and multiplies by signed coordinate.
Activity path in a channel reads on pulled configuration (including its
support). `born` preserves moments in full. Used after post-cutoff.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{k r t:ℕ}

lemma ax_step (s:Signed)(i:Axis): s.act (step i:Cover) = (if s.flip i then -step (s.perm i) else step (s.perm i)):=by
    ext j; obtain ⟨j,rfl⟩:=s.perm.surjective j; rw [Signed.act_at]; by_cases h:s.flip i<;>by_cases e:s.flip j<;>by_cases H:j=i<;> simp_all
lemma axial (s q:Signed)(p:Cover)(i:YForest G): tickW s p (tickW q 0 i)=tickW (s*q) p i:=by
    obtain ⟨⟨x,v⟩,j,rfl⟩:= every_stone i
    simp_rw [color_shove,Signed.mul_perm_apply,Signed.act_mul,Signed.act_add,Signed.act_zero,add_zero]
    unfold drift; simp only [Signed.mul_flip]; by_cases hp:q.flip v <;>by_cases hq:s.flip (q.perm v)<;>simp_all [stone,ax_step] <;> abel
lemma axial_id (x:YForest G): tickW 1 0 x=x:= by obtain ⟨⟨x,v⟩,j,rfl⟩:= every_stone x; simp [color_shove,drift]
def pendants (s:Signed) : Equiv.Perm (YForest G) := ⟨tickW s 0,tickW s⁻¹ 0,fun i=>by rw [axial, inv_mul_cancel,axial_id],fun i=>by rw [axial,mul_inv_cancel,axial_id]⟩
lemma ferries (s:Signed)(p:Cover)(i:YForest G) : tickW s 0 (jog p i)= jog (s.act p) (tickW s 0 i):=by
    obtain ⟨⟨x,v⟩,j,rfl⟩:= every_stone i
    rw [show jog p (stone (x,v) j)=stone (p+x,v) j from rfl,color_shove, color_shove,Signed.act_add]; refine Prod.ext ?_ rfl; change s.act p+s.act x+0+drift s v= s.act p+(s.act x+0+drift s v); abel

-- Geometry
lemma size_axis (s:Signed)(p:Cover): size (s.act p)=size p:=by unfold size; rw [← Equiv.sum_comp s.perm]; apply Finset.sum_congr rfl; intro i _; rw [Signed.act_at]; split<;>simp
lemma size_drift (s:Signed)(v:Axis): size (drift s v) ≤ 1:= by
    unfold drift; split; · rw [size_neg]; simp [size, apply_ite Int.natAbs]
    simp [size]
lemma room_axis (s:Signed)(x y:YForest G): terrain.gap (tickW s 0 x).1 (tickW s 0 y).1 ≤ terrain.gap x.1 y.1+2:=by
    obtain ⟨⟨x,i⟩,j,rfl⟩:= every_stone x; obtain ⟨⟨y,v⟩,k,rfl⟩:= every_stone y; simp_rw [color_shove,add_zero]
    change size (s.act y+_-(_+drift s i))≤ size (y-x)+_
    rw [show s.act y+drift s v-(s.act x+drift s i)= (s.act (y-x)+drift s v)+-drift s i by rw [Signed.act_sub]; abel]
    refine (size_add ..).trans ?_; have hh:=size_add (s.act (y-x)) (drift s v); rw [size_axis] at hh; have he:= size_drift s v; rw [size_neg]; have hz:=size_drift s i; omega
lemma axial_room (x:Fin r→YForest G)(s:Signed): soar terrain (tickW s 0 ∘ x) ≤ soar terrain x+2:= league_le Bank.terrain _ fun i j=> (room_axis s (x i) (x j)).trans (Nat.add_le_add_right (leg_le Bank.terrain (Prod.fst ∘ x) i j) 2)

-- orbits on all ranks positive or not
def veil (x:Fin r→ YForest G)(s:Signed):ℝ:= ∏ i,rimSign s (x i).2
lemma veil_norm (s:Signed)(x:Fin r→YForest G): |veil x s|=1:= by unfold veil rimSign; simp [Finset.abs_prod, apply_ite abs]
lemma veil_axial (x:Fin r→ YForest G)(s q:Signed) : veil x (s*q)= veil (tickW q 0 ∘ x) s*veil x q:=by
    unfold veil; rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun j _=>?_
    obtain ⟨⟨X,i⟩,v,h⟩:= every_stone (x j); rw [Function.comp_apply,← h]; rw [color_shove]; simp_rw [rim_stone,Signed.mul_flip]; by_cases H:q.flip i<;>by_cases e:s.flip (q.perm i)<;> simp_all
lemma veil_inv (x:Fin r→ YForest G)(s:Signed): veil (tickW s 0 ∘ x) s⁻¹= veil x s:=by
    have hz:=veil_axial x s⁻¹ s; rw [inv_mul_cancel,show veil x 1=1 by simp [veil,rimSign]] at hz
    have he:= veil_norm s x; cases le_total 0 (veil x s)<;> rename_i h; rw [abs_of_nonneg h] at he; nlinarith
    rw [abs_of_nonpos h] at he; nlinarith
-- monomial pull in positive-to-positive convention, passive basis compensates.
def pendant (s:Signed)(P:Ten ℝ (YForest G) r): Ten ℝ (YForest G) r:= fun x=> veil x s⁻¹ * P (tickW s⁻¹ 0 ∘ x)
lemma pendant_at (s:Signed)(P:Ten ℝ (YForest G) r)(x:Fin r→YForest G): pendant s P (tickW s 0 ∘ x)= veil x s*P x:= by
    rw [pendant,veil_inv,show tickW s⁻¹ 0 ∘ tickW s 0 ∘ x=x from funext fun i=> (pendants (G:=G) s).left_inv (x i)]
lemma gaze_stroll (s:Signed)(P:Ten ℝ (YForest G) r)(h:stroll P): stroll (pendant s P):=by
    intro b x
    unfold pendant; congr 1; rw [show tickW s⁻¹ 0 ∘ (⇑(jog b) ∘ x)=jog (s⁻¹.act b) ∘ (tickW s⁻¹ 0 ∘ x) from funext fun i=>ferries s⁻¹ b (x i)]; exact h ..
lemma gaze_paid {p C:ℝ}(s:Signed)(P:Ten ℝ (YForest G) r)(h:Amber Bank.terrain p C P)(he:0≤p): Amber Bank.terrain p (C*Real.exp (2*p)) (pendant s P):=by
    refine ⟨mul_nonneg h.1 (by positivity),fun x=>?_⟩
    let b:=Equiv.piCongrRight (fun _ : Fin r=> pendants (G:=G) s)
    obtain ⟨x,rfl⟩:= b.surjective x
    change ‖pendant s P (tickW s 0 ∘ x)‖ ≤ _; rw [pendant_at,norm_mul,Real.norm_eq_abs,veil_norm,one_mul]; apply (h.2 x).trans
    rw [mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ h.1; rw [Real.exp_le_exp]; have ht: (soar Bank.terrain (b x):ℝ)≤ (soar Bank.terrain x+2:ℝ):= by exact_mod_cast axial_room x s
    nlinarith only [he,ht]

-- Periodization covariance under moving the sites/read root.
lemma jog_lens (x:Fin (t+1)→YForest G)(b:Cover): salvo (jog b ∘ x)=salvo x:=by
    funext j; unfold salvo; change (_+_-(_+_):Cover) _= _; simp
lemma gooseLens (X:stars G t c)(w:Shift (Keys t)): salvo (goose w (stH X) (stR X))=w:=by
    ext1 ⟨i,a⟩; simp [salvo,goose,feetP]
lemma spine (X:stars G t c)(w:Shift (Keys t)): trope X w ↔ X= jog (X 0).1 ∘ foldUnder c ∘ goose w (stH X) (stR X):=by
    let z:=goose w (stH X) (stR X)
    constructor
    · intro h; funext i; refine Prod.ext ?_ rfl; change _=(X 0).1+wrap c (feetP w i); rw [add_comm]; exact eq_add_of_sub_eq (h i)
    intro e i; exact sub_eq_of_eq_add (by have p:=congr_arg Prod.fst (congr_fun e i); rw [add_comm (wrap c (feetP w i))]; exact p)
lemma goose_any (X:stars G t c)(z:Fin (t+1)→YForest G)(h:∀ i,(z i).2=(X i).2):
    goose (salvo z) (stH X) (stR X)= jog (-(z 0).1) ∘ z:=by
     funext i; refine Prod.ext ?_ (by have he:=h i; exact he.symm); change feetP _ _=-(z 0).1+_; rw [sole_salvo]; abel

def laneS (s:Signed)(X:stars G t c)(w:Shift (Keys t)) : Shift (Keys t):= salvo (tickW (G:=G) s 0 ∘ goose w (stH X) (stR X))
lemma target0 (s:Signed)(n:Side)(x:YForest G): foldUnder n (tickW s 0 x)=toss G s 0 (foldUnder n x):=by simpa using ticker s 0 x n
lemma folding_down (u:Co c (Hooks G)) : foldUnder c (Lattice.lift u.1,u.2)=u:= by simp [foldUnder]
lemma target1 (s:Signed)(n:Side)(i:YForest G)(x:Site n)(j:Hooks G)(h:i.2=j): (tickW s 0 i).2=(toss G s 0 (x,j)).2:=by
    obtain ⟨⟨u,v⟩,k,rfl⟩:= every_stone i; subst j; let y:=stone (lift x,v) k; have ht:foldUnder n y=(x,(stone (u,v) k).2):= folding_down (G:=G) (x,(stone (u,v) k).2)
    rw [← ht,← target0,color_shove]; change _=(tickW s 0 (stone (lift x,v) k)).2; rw [color_shove]; rfl
lemma target3 (s:Signed)(X:stars G t c)(w:Shift (Keys t)): let b:=tickW (G:=G) s 0 ∘ goose w (stH X) (stR X)
    goose (laneS s X w) (stH (toss _ s 0 ∘ X)) (stR (toss _ s 0 ∘ X))= jog (-(b 0).1) ∘ b:= by
    intro b; exact goose_any (toss _ s 0 ∘ X) b fun i=>target1 s c _ _ _ rfl
lemma turn_lane (s:Signed)(X:stars G t c)(w:Shift (Keys t)):
    laneS s⁻¹ (toss _ s 0 ∘ X) (laneS s X w)=w:=by
    let b:=goose w (stH X) (stR X); let y:=tickW s 0 (b 0)
    rw [laneS,target3]; change salvo (tickW s⁻¹ 0 ∘ (⇑(jog (-y.1)) ∘ tickW s 0 ∘ b))=_; rw [show tickW s⁻¹ 0 ∘ (⇑(jog (-y.1)) ∘ tickW s 0 ∘ b)=jog (s⁻¹.act (-y.1)) ∘ b from ?_,jog_lens]; exact gooseLens X w
    funext i; rw [Function.comp_apply,Function.comp_apply,ferries]; exact congr_arg (jog _) ((pendants s).left_inv (b i))
lemma untoss (s:Signed)(X:stars G t c): toss G s⁻¹ 0 ∘ (toss G s 0 ∘ X)=X:=by
    funext i; let y:YForest G:=(lift (X i).1,(X i).2); simp only [Function.comp_apply]; rw [← folding_down (X i),←target0,←target0]; exact congr_arg _ ((pendants s).left_inv y)
def borderP (s:Signed)(X:stars G t c): Shift (Keys t)≃ Shift (Keys t):= ⟨laneS s X,laneS s⁻¹ (toss _ s 0 ∘ X),turn_lane s X,fun w=> by have h:= turn_lane s⁻¹ (toss G s 0 ∘ X) w; rw [inv_inv,untoss] at h; exact h⟩
lemma tug (s:Signed)(X:stars G t c)(w:Shift (Keys t))(p:trope X w): trope (toss G s 0 ∘ X) (laneS s X w):=by
    let b:=goose w (stH X) (stR X); let a:= (X 0).1; let u:= tickW (G:=G) s 0 ∘ b
    have h:= (spine X w).mp p; have he i: (toss G s 0 ∘ X) i=jog (wrap c (s.act (lift a))) (foldUnder c (u i)):=by
        let y:=(b i); change toss _ s 0 _= _; rw [congr_fun h i]; change toss _ s 0 (jog a (foldUnder c (b i)))=_
        conv_lhs=> rw [←wrap_lift a]
        rw [← fold_move,← target0,ferries, fold_move]; rfl
    intro i; rw [he,he,laneS,sole_salvo,map_sub]; change _+_-(_+(_:Site c))=_; abel
lemma mask_trope (s:Signed)(X:stars G t c)(w:Shift (Keys t)): trope (toss G s 0 ∘ X) (laneS s X w) ↔ trope X w:=by
    refine ⟨fun p=>?_,tug s X w⟩
    have h:=tug s⁻¹ _ _ p; rw [untoss,turn_lane] at h; exact h
lemma flair_signed (s:Signed)(F:post G t)(X: stars G t c)(h:stroll F)(w:Shift (Keys t)):
    flair (toss G s 0 ∘ X) (pendant s F) (laneS s X w)=(∏ i, rimSign s (X i).2)*flair X F w:=by
    let b:=goose w (stH X) (stR X); by_cases p:trope X w
    · rw [flair_hit p,flair_hit ((mask_trope s X w).mpr p)]; unfold plantern; rw [target3,gaze_stroll s F h,pendant_at]; rfl
    rw [flair_miss p, flair_miss (fun z=> p ((mask_trope s X w).mp z)),mul_zero]
lemma wraps_pendant (s:Signed)(F:post G t)(h:stroll F)(n:Side):
    lagoon (pendant s F) n = (Blue.fade (markSign G s 0) (shine (lagoon F n))) (t+1):=by
    funext x
    obtain ⟨X,rfl⟩:= (Equiv.piCongrRight (fun _ : Fin (t+1)=> toss G (c:=n) s 0)).surjective x
    change lagoon _ _ (toss G s 0 ∘ X)= Blue.fade (markSign G s 0) (shine (lagoon F n)) (t+1) (toss G s 0 ∘ X); unfold fade
    rw [Finset.sum_eq_single X]
    · simp only [markSign,Matrix.of_apply,Function.comp_apply,↓reduceIte,shine_lit,smul_eq_mul]; unfold lagoon
      rw [← (borderP s X).tsum_eq (flair _ _),← tsum_mul_left]; exact tsum_congr fun i=> flair_signed s F X h i
    · intro y _ hy; obtain ⟨i,hi⟩:=Function.ne_iff.mp hy; rw [Finset.prod_eq_zero (Finset.mem_univ i),zero_smul]; simp [markSign,hi.symm]
    simp

end YM.WilsonCoeffUV.Bank.Mosaic
