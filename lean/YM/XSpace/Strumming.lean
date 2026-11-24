import YM.XSpace.WaveSpan
/-! # Free response tomography -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G:Gauge} {k n:ℕ}
section action
variable {D ι : Type*} [DecidableEq ι] [Fintype ι]

abbrev Channel (D ι: Type*) := poly (D×ι)

def electron (f:D→ℝ)(i:ι)(x:D×ι):ℂ:= if i=x.2 then (↑(f x.1):ℂ) else 0
def nex (f:D→ℝ)(i:ι) (p:Channel D ι):= slit (electron f i) p

def ionic (a b:D→ℝ) : Module.End ℂ (Channel D ι) := ∑ i:ι,(slit (electron b i)).toLinearMap.comp (slit (electron a i)).toLinearMap
lemma ionic_val (p:Channel D ι)(a b:D→ℝ):ionic a b p=∑ i:ι,nex b i (nex a i p):=by simp [ionic,nex]

def tune : List ((D→ℝ)×(D→ℝ))→Module.End ℂ (Channel D ι)
  | []=>LinearMap.id
  | v::vs=> (tune vs).comp (ionic v.1 v.2)

-- derivative pairing commuting
lemma ionic_comm (a b c d:D→ℝ)(p:Channel D ι): ionic a b (ionic c d p)=ionic c d (ionic a b p):= by
  rw [ionic_val _ _ d,map_sum,ionic_val _ _ b,map_sum]; simp_rw [ionic_val]; rw [Finset.sum_comm];
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  change nex b i _= _; unfold nex; rw [slit_slit _ (electron a i), slit_slit _ (electron b i), slit_slit (electron c j) (electron a i), slit_slit (electron c j) (electron b i)]
lemma tune_feed (p:Channel D ι)(a b:D→ℝ)(L): tune ((a,b)::L) p= tune L (ionic a b p):= rfl
lemma feed_tail (p:Channel D ι)(a b:D→ℝ)(L): tune ((a,b)::L) p= tune (L++[(a,b)]) p:= by
  induction L generalizing p with
  | nil=>rfl
  | cons c L IH =>
    obtain ⟨u,v⟩:=c
    rw [tune_feed,tune_feed,ionic_comm, List.cons_append,tune_feed,← IH]; rfl

lemma bilinear_ion (p:Channel D ι): ∃ F:(D→ℝ)→ₗ[ℝ] (D→ℝ)→ₗ[ℝ] Channel D ι, ∀ a b, F a b=ionic a b p:= by
  let IL (a b:D→ℝ)(i:ι):= nex b i (nex a i p)
  have he(f g:D→ℝ)(i:ι)(p:Channel D ι): nex (f+g) i p=nex f i p+nex g i p:= by unfold nex; rw [show electron (f+g) i=electron f i+electron g i by funext j; unfold electron; split <;>simp [*],slit_linear]
  have hr(f:D→ℝ)(i:ι)(p:Channel D ι)(t:ℝ): nex (t • f) i p=t • nex f i p:= by unfold nex; rw [show electron (t • f) i=(t:ℂ) • electron f i by funext j; unfold electron; split <;>simp [*], slit_smul]; exact Complex.coe_smul ..  -- inspect
  let F(i:ι) : (D→ℝ)→ₗ[ℝ] (D→ℝ)→ₗ[ℝ] Channel D ι:= {
    toFun a:=⟨⟨fun b=>IL a b i,fun b c=> he b c i _⟩,fun t b=> hr b i _ t⟩
    map_add' a b := LinearMap.ext fun c=> (show IL (a+b) c i= IL a c i+IL b c i by unfold IL; rw [he]; exact (slit _).map_add ..)
    map_smul' t a := LinearMap.ext fun c=> (show IL (t • a) c i= t • IL a c i by unfold IL; rw [hr]; exact (((slit (electron c i)).toLinearMap).restrictScalars ℝ).map_smul ..) }
  refine ⟨∑ i,F i,fun a b=>?_⟩; rw [ionic_val, LinearMap.sum_apply,LinearMap.sum_apply]; rfl
end action

abbrev Mark (G:Gauge)(n k:ℕ):= Channel (Deck n k) G.ColorIndex

def horizon (x:Points n)(G:Gauge)(k:ℕ)(i:Deck n k×G.ColorIndex): WebKey G→₀ ℂ := limbs (x i.1.1) (flavor _ i.2 (pieces _ i.1.2.2))

def score (x:Points n)(G:Gauge)(k:ℕ):Mark G n k→ₐ[ℂ] Web G:= Normal.exchange (horizon x G k)
def energy (x:Points n)(G:Gauge)(k:ℕ):= Normal.scope (horizon x G k) (net G)
lemma score_one (x:Points n) (i): score x G k (X i)=factors (x i.1.1) (flavor _ i.2 (pieces _ i.1.2.2)):=by rw [strokes]; unfold score; rw [exchange_x]; rfl
lemma score_keeps (x:Points n) (p:Mark G n k): Kept (emitters x) (score x G k p):= by
  induction p using MvPolynomial.induction_on with
  | C a=> unfold score; rw [exchange_c]; exact fun i hi=>by simp at hi
  | add p q hp hq=> rw [map_add]; exact hp.add hq
  | mul_X p i h=> rw [map_mul,score_one]; exact h.mul (Kept.posted (allt x _) _)
lemma score_read (x:Points n)(p:Mark G n k): WW G (score x G k p)= Normal.blend (energy x G k) 0 p:= by unfold WW score energy; rw [Normal.wets,show Normal.reads _ 0=0 from _root_.funext fun i=>Finsupp.linearCombination_zero_apply ..]
lemma score_D (x:Points n)(p:Mark G n k){z:E4}(q:Flavor 0)(c i:G.ColorIndex)(hz:z∉emitters x): scrape z q i (score x G k p)=score x G k (nex (fromFace x c z q) i p):= by
  induction p using MvPolynomial.induction_on with
  | C a=> unfold score nex scrape; simp
  | add p q hp hq=> unfold nex at *; rw [_root_.map_add, _root_.map_add, _root_.map_add (slit _),_root_.map_add,hp,hq]
  | mul_X p j H=>
    have he:scrape z q i (score x G k (X j))=score x G k (slit (electron (fromFace x c z q) i) (X j)):= by
      have hx:= ne_of_mem_of_not_mem (allt x j.1.1) hz
      rw [score_one, through_eqn hx.symm q _ c, slit_X]; unfold score electron; rw [exchange_c]
      by_cases hj:i=j.2
      · rw [if_pos hj,if_pos hj.symm]; apply congr_arg; apply congr_arg Complex.ofReal
        let u:=flavor 0 c q;let v:= flavor _ c (pieces _ j.1.2.2)
        have ht:= Maxwell.exchange v u (show x j.1.1-z∈away from sub_ne_zero.mpr hx); change legKernel v u _=legKernel u v _ at ht; rw [neg_sub] at ht; exact ht.symm
      rw [if_neg hj,if_neg (Ne.symm hj)]
    unfold nex at *; rw [map_mul (score x G k), (scrape z q i).leibniz, he,H, (slit _).leibniz]; simp only [smul_eq_mul,map_add,map_mul]

abbrev Bunch:= (E4×Flavor 0)× (E4×Flavor 0)

def coded (x : Points n)(c:G.ColorIndex)(k) (l:List Bunch) := l.map (fun w=> (fromFace (k:=k) x c w.1.1 w.1.2, fromFace (k:=k) x c w.2.1 w.2.2))

def curtain (G:Gauge): List Bunch→ Web G
| []=>1
| z::l=> signFor z.1.1 z.2.1 z.1.2 z.2.2 G*curtain G l

def Clear (B:Finset E4) : List Bunch→ Prop
| []=>True
| z::l=> z.1.1≠ z.2.1 ∧ z.1.1∉B ∧ z.2.1∉B ∧ Clear (insert z.1.1 (insert z.2.1 B)) l
lemma of_cloud {B:Finset E4}{l:List Bunch}(h:Clear B l): Thread G B (curtain G l):=by
  induction l generalizing B with
  | nil=>exact Thread.one
  | cons z l ih=> obtain ⟨a,b,c,d⟩:=h; exact Thread.join _ _ a b c (ih d)
lemma coded_connections (x:Points n)(c:G.ColorIndex){B:Finset E4}{l:List Bunch}(h: Clear B l)(he:emitters x⊆ B) (p:Mark G n k):
    Normal.blend (skim G (emitters x)) 0 (curtain G l* score x G k p) = Normal.blend (energy x G k) 0 (tune (coded x c k l) p):= by
  induction l generalizing p B with
  | nil=> rw [curtain,one_mul,skim_interior _ (score_keeps x p),score_read]; rfl
  | cons z l ih=>
    obtain ⟨a,b,d,s⟩:= h
    let Y:=curtain G l
    let U:=emitters x; let hx:z.1.1∉U:=Finset.notMem_mono he b
    let hy:z.2.1∉U:= Finset.notMem_mono he d
    rw [curtain,remote U z.1.1 z.2.1 _ _ hx hy ((of_cloud s).mono (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ he))) (score_keeps x p)]
    simp_rw [score_D x p _ c _ hx, score_D x _ _ c _ hy];
    let H:=coded x c k [z]; rw [coded,List.map_cons,tune_feed,ionic_val,map_sum,map_sum]
    apply Finset.sum_congr rfl; intro i _; exact ih s (he.trans (fun v hv=> Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))) _

lemma voice_open (x:Points n)(c:G.ColorIndex)(h:x∈conf _)(P:Mark G n k)(H:Silent (emitters x) (score x G k P)) (l:List ((Deck n k→ℝ)× (Deck n k→ℝ))):
    Normal.blend (energy x G k) 0 (tune l P)=0:= by
  let S:= Deck n k→ℝ; let U:=emitters x; let σ:=Normal.blend (energy x G k) 0
  suffices he: ∀ (V:Finset E4),U⊆V→∀ Q:Mark G n k,(∀ m:List Bunch,Clear V m→ σ (tune (coded x c k m) Q)=0) → σ (tune l Q)=0 from he U (Finset.Subset.refl _) P (fun m hm=> by unfold σ; rw [← coded_connections x c hm (Finset.Subset.refl _)]; exact skim_subs _ c H (of_cloud hm))
  induction l with
  | nil=> exact fun V _ Q h=> h [] trivial
  | cons a l ih=>
    obtain ⟨a,b⟩:=a; intro V he Q hv
    obtain ⟨F,hF⟩:= bilinear_ion (D:=Deck n k) Q
    let L:= F.compr₂ ((σ.comp (tune l)).restrictScalars ℝ)
    have hh (U:Finset E4) (he:emitters x⊆U)(v:S):v ∈ Submodule.span ℝ {a:S|∃ y∉U,∃ p:Flavor 0, a=fromFace x c y p}:= waves_launch x k h U he c ▸ Submodule.mem_top
    suffices L=0 by rw [tune_feed,← hF]; exact DFunLike.congr_fun (DFunLike.congr_fun this a) b
    refine LinearMap.ext_on (waves_launch x k h _ he c) ?_
    rintro v ⟨y,hy,p,rfl⟩; refine LinearMap.ext_on (waves_launch x k h (insert y V) (he.trans (Finset.subset_insert ..)) c) ?_
    rintro w ⟨z,hz,g,rfl⟩
    change σ (tune l (F _ _))=0; rw [hF];
    refine ih (insert y (insert z V)) (he.trans (fun i hi=> Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi))) _ (fun m hm=>?_) --
    have ht:z≠y ∧ z∉V := by simpa only [Finset.mem_insert,not_or] using hz
    exact hv (((y,p),(z,g))::m) ⟨ht.1.symm,hy,ht.2,hm⟩

variable {A J:Type*} [DecidableEq J] [Fintype J]
lemma tune_heat (p:Channel A J)(K:Normal.Symmetric (A × J))(v):tune v (milk K p)=milk K (tune v p):= by
  induction v generalizing p with
  | nil=>rfl
  | cons v l ih=>
    obtain ⟨a,b⟩:=v; rw [tune_feed, tune_feed, show ionic a b (milk K p)=milk K (ionic a b p) from ?_,ih]; simp_rw [ionic_val,_root_.map_sum,nex,Normal.skims]

def Hide (p:Channel A J):Prop := ∀ l:List ((A→ℝ)×(A→ℝ)), MvPolynomial.aeval (0:A × J→ℂ) (tune l p)=0
lemma licensed (x:Points n)(c:G.ColorIndex)(h:x∈conf _)(P:Mark G n k)(H:Silent (emitters x) (score x G k P)): Hide (milk (energy x G k) P) := by intro l; rw [tune_heat]; exact voice_open x c h P H l
end YM.XSpace.Stab
