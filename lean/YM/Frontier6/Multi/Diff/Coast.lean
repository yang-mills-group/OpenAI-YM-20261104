import YM.Frontier6.Multi.Diff.Priced

/-! Output appearance at deepest band. Physicalized use with Realm, horizon
    quantifiers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway Tale Spec Lattice Extraction Cells Next.UVStress Org Next.Extract Bid Dash
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I J V:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}{T : Fareway I}{a b c ε:ℝ}
set_option quotPrecheck false
structure Ribbon (C:Family G)(F:Extraction.Order)(S:Table C.book) : Prop where
   base : ∃ (t:Table C.book)(m:ℕ→Table C.book)(R:Bin t)(Y:DiffPlan S),Base C F t m R S Y
   realm : PhysicalNext.Repeat.Legato.Realm C
   grill : Org.Grill C F
   selection : Extraction.Wcmain C
   simply : G.Simple
variable (K: Final C F S) (hC: Ribbon C F S) {x:I→ V→ E4} (v:V→ S.Tag)(d:ℕ)
def grades (v:V→S.Tag)(i:V) : ℕ:= (v i).1
def load (v:V→S.Tag):ℝ:= σ (grades v)
def Paces {x:I→ V→ E4} (T:Fareway I)(S:Schedule)(k:I→ℕ):Prop:= ∀ z:V×Axis,∀ᶠ i in T.via, period (x i) (S.a (k i)) z
def CoverWalk (x:I→V→ E4)(T:Fareway I)(S:Schedule)(k:I→ℕ): Prop:= ∀ᶠ i in T.via,(∃ v:V→ Cover,x i=S.gridPoint (k i)∘ v)∧∀ a:Axis,Injective (fun j=> x i j a)
variable {S':Schedule}{j k m:I→ℕ}
lemma Paces.strides (h:Paces (x:=x) T S' k) : CoverWalk x T S' k:= (eventually_all.mpr h).mono fun i hi=> ⟨period_to_cover S' _ hi,period_injective _ _ hi (S'.a_pos _)⟩
lemma CoverWalk.chooseWalk (h:CoverWalk x T S' k): ∃ v:I→V→ Cover,x=ᶠ[T.via](fun i=>S'.gridPoint (k i) ∘ v i):=by
    let Q(i:I):=(∃ v:V→ Cover, x i=S'.gridPoint (k i) ∘ v); let v(i:I):V→ Cover:= if h:Q i then h.choose else 0; refine ⟨v,h.mono (fun i hi=>?_)⟩; dsimp only; unfold v; rw [dif_pos (show Q i from hi.1)]; exact Exists.choose_spec (show Q i from hi.1)
lemma presentations : ∃ p:∀ i:V,C.label (grades v i), (fun i:V=> S.classTokens (⟨grades v i,p i⟩ : C.book.Token))=v:=by
    choose p hp using fun i:V=> S.onto _ (v i).2; refine ⟨p,funext fun i=>?_⟩; change (⟨_,S.project (v i).1 (p i)⟩:S.Tag)= _; rw [hp]
lemma throughShift (d:ℕ) {x:V→E4} (c:E4)(v:V→ S.Tag): absorb K c d (assembly S (fun i=>x i+c) v)= absorb K 0 d (assembly S x v):= congr_arg (capture K d) <| funext fun u=> funext fun m=>funext fun p=>funext fun Z=> united K c u x v Z p

section
variable [Nonempty V]
include hC
lemma fleeting (hh:Aspect T x)(hj:CoverWalk x T C.S j)(hx: Bench C.S T j c)(hm:Bench C.S T m a)(hk:Bench C.S T k b) (hc:1<c)(hε:0<ε)(ha:a<1)(hb:b<a)(ht:0<b):
    let X(i:I)(p:E4):= assembly S (fun z=>x i z +p) v
    let ψ:= forestPower (grades v) a c ε; let f(i:I):= absorb K 0 d (assembly S (x i) v); let Z(i:I)(p:E4):=letter S p ⟨d,f i⟩
    let ξ:= Ultrafilter.of F.fuse
    (∀ w:Fin (d+1), T.Costs (fun i=> weight K w (reach K d w (f i))) (ψ-(w:ℝ)*a))∧ Permit K T ξ j k X (ψ+b) ∧ Permit K T ξ j k Z (ψ+b) ∧
    Permit K T ξ j k (fun i p=> X i p-Z i p) (ψ+b-d*(a-b)^2):=by
    intro X ψ f Z ξ; have hξ:ξ.toFilter ≤ F.fuse:= Ultrafilter.of_le _
    obtain ⟨z,hZ⟩:=hj.chooseWalk; let y (i:I):= C.S.gridPoint (j i) ∘ z i
    have hg(ζ:I):x ζ=y ζ→ X ζ=(fun p=> assembly S (fun z=> y ζ z+p) v):=fun he=> by unfold X; rw [he];
    obtain ⟨p,hp⟩:=presentations v; let V':=fun i:V=> S.classTokens (⟨grades v i,p i⟩: C.book.Token); let X'(i:I)(p:E4):= assembly S (fun z=> y i z+p) V'
    have he:X=ᶠ[T.via] X':= hZ.mono fun i hi=> by rw [hg i hi]; unfold X'; rw [show V'=v from hp]
    let f'(i:I):= absorb K 0 d (X' i 0); let Z' (i:I)(p:E4):=letter S p ⟨d,f' i⟩; have hF:f'=ᶠ[T.via]f:=he.mono fun i hi=>by unfold f'; rw [← hi]; simp only [X,add_zero];rfl
    obtain ⟨t,m',R,Y,h⟩:= hC.base
    let U:= Aspect.cf hh hZ; let W:= hC.selection; let G:= hC.grill; let C':= hC.realm
    let O : V := Classical.choice inferInstance
    have hM:∀ᶠ i in T.via,∀ a:Axis,Injective fun j=> y i j a:= by filter_upwards [hj,hZ] with i ⟨hj,hw⟩ hz; rw [←(show x i=y i from hz)]; exact hw
    have hA:(∀ᶠ i in T.via,∀ a:Axis,Injective (fun b=> (C.S.gridPoint (j i) (z i b)) a)) := hM
    refine ⟨fun w=>(nearEnough K h C' hC.simply G W hξ hx hm (grades v) p z O ha hc hε U hA d (ht.trans hb) w).cf (hF.mono (fun i hi=>?_)), ?_, ?_, ?_⟩
    · change weight _ _ (reach K d w (f' i))=_; rw [hi]
    · refine (liftoff K h C' hC.simply G W hξ hx hm hk (grades v) p z O ha hc ht hb hε U hA d).same ?_; filter_upwards [he] with i hi x; change Tale.Congr K (X' i x) _; rw [← hi]; exact almost K _
    · refine (gram K h C' hC.simply G W hξ hx hm hk (grades v) p z O ha hc ht hb hε U hA d).same ?_; filter_upwards [hF] with i hi x; change Tale.Congr K (letter S x ⟨d,f' i⟩) _; rw [hi]; exact almost K _
    refine (citation K h C' hC.simply G W hξ hx hm hk (grades v) p z O ha hc ht hb hε U hA d).same ?_; filter_upwards [he,hF] with i hi h x; change Tale.Congr K (X' i x-letter S x ⟨d,f' i⟩) _; rw [←hi,h]; exact almost K _

lemma ample (hh:Aspect T x) (w:Fin (d+1)): T.Costs (fun i=> weight K w (reach K d w (absorb K 0 d (assembly S (x i) v)))) (load v-(w:ℝ)):=by
   intro b hb; let f(t:ℝ):= forestPower (grades v) (1-t) (1+t) t-(w:ℝ)*(1-t)
   have hF: f 0<b:=by unfold f forestPower; simpa only [sub_zero,add_zero,mul_one,sub_self,mul_zero,zero_mul,sub_right_inj] using! hb
   have hc:Continuous f:=by unfold f forestPower; fun_prop
   obtain ⟨t,ht,hZ,hY⟩:= ((show ∀ᶠ t:ℝ in 𝓝[>] 0,0 < t from self_mem_nhdsWithin).and (eventually_nhdsWithin_of_eventually_nhds ((hc.continuousAt.eventually (gt_mem_nhds hF)).and (show ∀ᶠ t:ℝ in 𝓝 0,t<1/2 from gt_mem_nhds (by norm_num))))).exists
   let c:=1+t; let a:=1-t; have hz:1/2<a:=by unfold a; linarith
   have hc:1<c:=by unfold c; linarith
   obtain ⟨j,hj⟩:= picks C.S C.path.levels.fits.mesh T c (one_pos.trans hc); obtain ⟨m,hm⟩:= picks C.S C.path.levels.fits.mesh T a ((half_pos one_pos).trans hz); obtain ⟨k,hk⟩:= picks C.S C.path.levels.fits.mesh T (1/2) (half_pos one_pos)
   let F:= weight K w ∘L reach K d w; let U:= F.restrictScalars ℝ
   have hh':Guard T x (fun i=>C.S.a (j i)) c (fun _ x=>U (absorb K 0 d (assembly S x v))) (f t):= shunned K hC.grill v d U hh hj.spacing hc; exact hh'.alive hj.spacing.pay (fun _=>C.S.a_pos _) (fun y hy h=>(fleeting K hC v d (hh.peal hy hc) (Paces.strides h) hj hm hk hc ht (sub_lt_self _ ht) hz (half_pos one_pos)).1 w) b hZ
end
end YM.Frontier6.Road
