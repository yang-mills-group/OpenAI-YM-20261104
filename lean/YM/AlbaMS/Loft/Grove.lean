import YM.AlbaMS.Loft.Capital
import YM.AlbaMS.Distributions.Directions

/-! Produce supergerms with inert direction variables. Vec pull as needed.
Only evaluates around identity link field, no assertions about a globally chosen log branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Loft.Chart
open Set Function Filter Analysis Bric
open scoped BigOperators Classical Topology ContDiff
variable {E X Y : Type*} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {x:X} {f g : X→ℝ} {m n : ℕ}
open Testing

abbrev Grove (X : Type*)[NormedAddCommGroup X][NormedSpace ℝ X] := {f:X→ℝ // ContDiffAt ℝ ω f 0}
lemma nd_germ {f g:X→Y}(h:f=ᶠ[𝓝 x]g)(l:List X): nd l f=ᶠ[𝓝 x] nd l g:= by
  induction l generalizing g f with|nil=>exact h|cons i t ih=>
    exact ih ((h.fderiv (𝕜:=ℝ)).mono fun _ he=> DFunLike.congr_fun he i)
lemma nd_and (p : Fin m→X)(f : X→Y)(h:ContDiffAt ℝ ω f x): nd (List.ofFn p) f x=iteratedFDeriv ℝ m f x p:=by
  induction m generalizing f with|zero=>simp|succ m ih=>
    rw [List.ofFn_succ,nd_cons,ih _ (D (p 0) f) (dSmooth h _ (by simp))]; have he:=cons_inner (j:=m) (x:=x) (h.of_le le_top) (p 0) (Fin.tail p); rw [Fin.cons_self_tail] at he; exact he.symm
lemma nd_local (l : List X)(F : X→Y)(h:ContDiffAt ℝ ω F x): nd l F x=iteratedFDeriv ℝ l.length F x l.get:=by rw [← nd_and l.get F h,List.ofFn_get]
namespace Grove -- rename? redundant
variable (F G : Grove X)
instance : FunLike (Grove X) X ℝ:=⟨Subtype.val,Subtype.val_injective⟩
instance : Add (Grove X) := ⟨fun F G=> ⟨F.val+G.val,F.2.add G.2⟩ ⟩
instance : Sub (Grove X):=⟨fun F G=>⟨F.val-G.val,F.2.sub G.2⟩⟩
instance : Mul (Grove X):=⟨fun F G=>⟨F.val* G.val,F.2.mul G.2⟩⟩
instance : SMul ℝ (Grove X):=⟨fun c F=>⟨c • F.val, F.2.const_smul c⟩⟩
def dx (i:X)(F:Grove X): Grove X:=⟨D i F.val,dSmooth F.2 i (by simp)⟩
variable {ι κ:Type*}{ρ:ι→Bool}{σ:κ→Bool}

structure Brook (ρ : ι→Bool)(X:Type*)[Zero X] where
   stream : ι → X
   empty i : ρ i=true → stream i=0
namespace Brook
variable (B:Brook ρ X)
private lemma swapp (u v : X): (dx u (dx v F)).val=ᶠ[𝓝 0](dx v (dx u F)).val:= (F.2.eventually (by simp)).mono (fun x hx=> commuteD (hx.of_le le_top) u v)
private lemma dz (i l): nd (List.map B.stream (i::l)) F.val = nd (l.map B.stream) (dx (B.stream i) F).val:=rfl -- v unused binder fix
private lemma absent {i:ι}(p:B.stream i=0)(l:List ι): nd (l.map B.stream) (dx (B.stream i) F).val=0:= by rw [p,dx]; change nd _ (Analysis.D 0 _) = _; rw [show Analysis.D 0 F.val=0 from funext (fun _=>map_zero _),nd_zero]
private lemma quiet (a l : List ι)(i j : ι): nd ((a++i::j::l).map B.stream) F.val 0= sting (ρ i && ρ j) (nd ((a++j::i::l).map B.stream) F.val 0):= by
  induction a generalizing F with
  |cons v a ih=> simp only [List.cons_append,List.map_cons]; exact ih (dx (B.stream v) F)
  |nil=>
    simp only [List.nil_append]; have he : nd (List.map B.stream (i::j::l)) F.val 0=nd (List.map B.stream (j::i::l)) F.val 0:= (nd_germ (swapp F _ _) _).eq_of_nhds; rw [he]; cases hi:ρ i<;> cases hj:ρ j <;> first|rfl|skip
    rw [dz, absent F B (B.empty _ hj)]; simp

def shine (B:Brook ρ X)(F : Grove X): Coil ρ ℝ:=⟨fun l=> nd (l.map B.stream) F.val 0,quiet F B⟩
lemma shines (l): shine B F l=nd (l.map B.stream) F.val 0:=rfl
lemma lit0 : shine B F []= F.val 0:=rfl
lemma litD (i): Coil.D i (shine B F)= shine B (dx (B.stream i) F):=rfl
lemma evaporate {i}(h:B.stream i=0): Coil.D i (shine B F)=0:= Coil.ext _ _ (fun l=> show nd (l.map B.stream) _ _=_ from congr_fun (absent F B h l) (0:X)) -- fix
lemma bright : Coil.Tone false (shine B F):=by
  intro l; induction l generalizing F with|nil=>intro _;rfl|cons i l ih=>
    intro he; cases h:ρ i; · rw [band_cons,h, ih (dx (B.stream i) F) he]; rfl
    exact False.elim (he (DFunLike.congr_fun (evaporate F B (B.empty _ h)) l))
lemma shadow (h:F.val=ᶠ[𝓝 0]G.val): shine B F=shine B G:= Coil.ext _ _ fun l=> (nd_germ h (l.map B.stream)).eq_of_nhds
lemma gleam_add : shine B (F+G)=shine B F+shine B G:= by
  ext l; induction l generalizing F G with|nil=>rfl|cons i l ih=>
    have he:=F.2.eventually (by simp); have ht:= G.2.eventually (by simp); rw [← Coil.D_read,← Coil.D_read (F:=_+_), map_add, litD,litD,litD, ← ih]; refine DFunLike.congr_fun (shadow _ _ B ?_) l
    filter_upwards [he,ht] with x h hh
    change fderiv ℝ (F.val+G.val) x _=fderiv ℝ _ x _+fderiv ℝ _ x _; rw [fderiv_add (h.differentiableAt (by simp)) (hh.differentiableAt (by simp))]; rfl
lemma gleam_sub : shine B (F-G)=shine B F-shine B G:= by
  apply eq_sub_of_add_eq; rw [← gleam_add]; congr; exact Subtype.ext (sub_add_cancel _ _) -- tactic
lemma gleam_smul (c:ℝ): shine B (c • F)=c • shine B F:=by
  ext l; induction l generalizing F with|nil=>rfl|cons i l ih=>
    rw [← Coil.D_read,← Coil.D_read (F:=c • _), map_smul,litD,litD,← ih]; refine DFunLike.congr_fun (shadow _ _ B ?_) l; filter_upwards [F.2.eventually (by simp)] with x h
    change fderiv ℝ (c • F.val) x _=c • (fderiv ℝ _ x _); rw [fderiv_const_smul (h.differentiableAt (by simp))]; rfl
lemma gleam_mul : shine B (F*G)=shine B F*shine B G:=by
  ext l; induction l generalizing F G with|nil=>rfl|cons i l ih=>
    rw [← Coil.D_read,← Coil.D_read (F:=_ *_), Coil.mulD,(bright F B).pl,Bool.and_false,sting_false,litD,litD,litD]; rw [Coil.plus_read,← ih, ← ih, ← Coil.plus_read, ← gleam_add]; refine DFunLike.congr_fun (shadow _ _ B ?_) l; filter_upwards [F.2.eventually (by simp),G.2.eventually (by simp)] with x h hl
    change fderiv ℝ (F.val*G.val) x _= (fderiv ℝ _ x _) * _ + _* fderiv ℝ _ x _; rw [fderiv_mul (h.differentiableAt (by simp)) (hl.differentiableAt (by simp))]; simp [mul_comm,add_comm] -- fix
-- sums bridge through eventual equality measures
lemma vanish (h:F.val=ᶠ[𝓝 0]0):shine B F=0:=by ext l; rw [shines, (nd_germ h _).eq_of_nhds,nd_zero];rfl
lemma constant (c:ℝ)(h:F.val=ᶠ[𝓝 0] fun _=>c): shine B F=Coil.put ρ c:=by
  ext l; rw [shines, (nd_germ h _).eq_of_nhds]; cases l with|nil=>rfl|cons i l=>rw [List.map_cons,nd_const_nonempty];rfl
lemma flash {E : Type*} (v:Finset E)(U:E→ Grove X)(h:F.val=ᶠ[𝓝 0] (∑ i∈v,(U i).val)):
    shine B F=∑ i∈v,shine B (U i):=by
  induction v using Finset.induction_on generalizing F with
  | empty=>rw [Finset.sum_empty] at h ⊢; exact vanish F B h
  | @insert i t ht ih=>
    rw [Finset.sum_insert ht] at h ⊢; refine (eq_add_of_sub_eq' ?_); rw [← gleam_sub]; apply ih; filter_upwards [h] with x hx; change F.val x-_= _; rw [hx]; change (U i).val x+_-_= _; rw [add_sub_cancel_left]

variable (C:Brook σ Y)(L:X →L[ℝ]Y)
def dive (F:Grove Y) (L:X→L[ℝ]Y): Grove X:=⟨F.val ∘ L,(by apply ContDiffAt.comp (g:=F.val) (f:=L) (0:X) _ L.contDiff.contDiffAt; rw [map_zero]; exact F.2)⟩
variable {s:Finset κ}(A:κ→ι→ℝ)(u:Coil.Routes σ ρ A)
lemma crossed (P:Grove Y)(h:∀ i,L (B.stream i)=∑ j∈s,A j i • C.stream j): shine B (dive P L)= Coil.shot s A u (shine C P):=by
  ext l; induction l generalizing P with|nil=> change _=(shine C P) [];rw [lit0,lit0];change P.val (L 0)=_;rw [map_zero]
                                         |cons i l ih=>
    let W j : Grove X:=dive (dx (C.stream j) P) L
    have he : (dx (B.stream i) (dive P L)).val=ᶠ[𝓝 0] ∑ j∈s,(A j i) • (W j).val:=by
      have H:=L.continuous.tendsto (0:X); rw [map_zero] at H; filter_upwards [H.eventually (P.2.eventually (by simp))] with x hx
      change fderiv ℝ (P.val ∘ L) _ _=_; rw [fderiv_comp x (hx.differentiableAt (by simp)) L.differentiableAt,L.fderiv]; simp_rw [ContinuousLinearMap.comp_apply,h,map_sum,map_smul]; rw [Finset.sum_apply]
      rfl
    rw [← Coil.D_read,← Coil.D_read (F:=Coil.shot _ _ _ _), litD, flash _ B s (fun j=> (A j i) • W j) he,Coil.shot_D, Coil.drip_apply,map_sum]; simp_rw [Coil.sum_read,gleam_smul, litD, map_smul,Coil.smul_read, W,ih]
lemma lit_sheet (F : X→L[ℝ] ℝ) (s:Finset ι)(h: ∀ i,i∉s→ F (B.stream i)=0): shine B ⟨F,F.contDiff.contDiffAt⟩=∑ i∈s,F (B.stream i) • Coil.varC ℝ ρ i:=by
  let G : Grove X:=⟨F,F.contDiff.contDiffAt⟩; change shine B G=_; apply Coil.deep
  · rw [Coil.sum_read]; simp only [Coil.smul_read,Coil.var_nil,mul_zero,Finset.sum_const_zero]; exact map_zero F
  intro x; rw [litD,constant _ B (F (B.stream x)) (Filter.Eventually.of_forall (fun z=> by change fderiv ℝ F z _=_;rw [F.fderiv])),map_sum]; simp_rw [map_smul,Coil.varD]; rw [Finset.sum_eq_single x]; rw [if_pos rfl,← Coil.put_smul_left,mul_one]
  intro i _ hi; rw [if_neg (Ne.symm hi),smul_zero]; intro hh; rw [h x hh,zero_smul]
end Brook
end Grove
end YM.MSBar.Loft.Chart
