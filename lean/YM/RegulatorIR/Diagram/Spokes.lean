import YM.RegulatorIR.Diagram.Drained
import YM.RegulatorIR.Budget.Draft

/-! Restore external field legs after the heat step. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram
open MvPolynomial Budget Budget.Layer Budget.Packet Budget.Tuple Function Finset
open scoped Topology BigOperators Classical
variable {I J:Type} [Fintype I][Fintype J] {r :ℕ}

def tunes (F: Fin r → I → ℝ) (z:Tuple I r) := ∏ i,F i (z i)
def listen (T:Packet I r) (F: Fin r→ I → ℝ) := ∑ z:Tuple I r,T z*tunes F z
lemma play (T:Packet I r)(v:I→ℝ): listen T (fun _=>v)=eval v (render T):=by simp only [render,map_sum,eval_mul,eval_C,word, map_prod,eval_X];rfl

def announce (K:Layer I I)(b:I→ℝ)(x:I) := ∑ y, K y x*b y
lemma ray_voice (T : Packet I r)(K:Layer I I)(F:Fin r→ I→ℝ)(i:Fin r): listen (ray i T K) F=listen T (update F i (announce K (F i))):=by
 unfold listen ray; simp_rw [tsum_fintype,sum_mul]
 let g (v:Tuple I r × I):= swivel i T K v.1 v.2*tunes F v.1
 rw [← Fintype.sum_prod_type (f:=g), ← Equiv.sum_comp (Tuple.exchange i) g, Fintype.sum_prod_type]
 apply sum_congr rfl;intro a _
 let C : (Fin r→I→ℝ)→Tuple I r→ℝ:= fun F z=>∏ k∈(univ.erase i),F k (z k)
 have he (U : Fin r→ I→ℝ)(z:Tuple I r) : tunes U z= U i (z i)*C U z:= (mul_prod_erase _ _ (mem_univ i)).symm
 let U:=update F i (announce K (F i))
 have H v : g ((Tuple.exchange i) (a,v)) = T a*(K v (a i)*F i v*C F a):=by
    unfold g; change swivel i T K (update a i v) _*tunes F (update a i v)= _; unfold swivel
    simp only [Function.update_self]; rw [show (Tuple.exchange i (a,v)).2=a i from rfl,update_idem,Function.update_eq_self, he,update_self]
    rw [show C F (update a i v)=C F a from Finset.prod_congr rfl fun k hk=>by rw [update_of_ne (ne_of_mem_erase hk)]]; ring
 simp_rw [H,← Finset.mul_sum,←Finset.sum_mul]
 change T a * (announce K (F i) (a i)* C F a)= _; rw [he,update_self]; exact congr_arg (fun x:ℝ=>T a*(announce K (F i) (a i)*x)) (show C F a=C U a from Finset.prod_congr rfl fun k hk=>by unfold U; rw [update_of_ne (ne_of_mem_erase hk)])
lemma sequence_listen (T:Packet I r)(K:Layer I I)(F:Fin r→I→ℝ)(b:List (Fin r))(h:b.Nodup) :
    listen (drawing T K b) F=listen T (fun i=> if i∈b then announce K (F i) else F i):=by
 induction b generalizing F with
 | nil=> simp [drawing]
 | cons i v ih=>
    unfold drawing; rw [ray_voice,ih _ (List.nodup_cons.mp h).2];apply congr_arg (listen T)
    ext1 j
    by_cases hv:i=j
    · subst j; simp [(List.nodup_cons.mp h).1]
    simp [Ne.symm hv]
lemma draft_rendered (T:Packet I r)(K:Layer I I)(b:I→ℝ): eval b (render (draft K T))=eval (announce K b) (render T):=by rw [draft,render_symmetry,← play, sequence_listen,←play]; simp; exact List.nodup_finRange _

variable (f:I↪ J)
lemma offer_render (T:Packet I r)(v:J→ℝ): eval v (render (offer f T)) = eval (v ∘ f) (render T):=by
 rw [←play,←play]; unfold listen
 rw [← tsum_fintype (L:=SummationFilter.unconditional _),← tsum_fintype (L:=SummationFilter.unconditional _)]; rw [← (injectT f).tsum_eq]
 · simp_rw [offer_eq];rfl
 intro i h; by_contra! h'; apply h; dsimp only; rw [offer_zero _ h',zero_mul]

def dilute (v:I→ℝ)(j:J) := Stalk.collect f v j
omit [Fintype I][Fintype J] in
lemma dilute_here (v:I→ℝ)(i) : dilute f v (f i)=v i := by
 unfold dilute Stalk.collect; apply tsum_eq_single (f:=fun z:Stalk f (f i)=>v z.val) (b:=⟨i,rfl⟩); intro z hz; exact (hz (Subtype.ext (f.injective z.property))).elim
omit [Fintype I][Fintype J] in
lemma dilute_miss (v:I→ℝ)(x:J)(h:x∉Set.range f): dilute f v x=0:= by
 unfold dilute Stalk.collect; haveI : IsEmpty (Stalk f x):=⟨fun z=>h ⟨z.val,z.property⟩⟩; exact tsum_empty
lemma crop_render (T:Packet J r)(v:I→ℝ): eval (dilute f v) (render T)=eval v (render (crop f T)):=by
 rw [← play,← play];unfold listen; rw [← tsum_fintype (L:=SummationFilter.unconditional _),← tsum_fintype (L:=SummationFilter.unconditional _),← (injectT f).tsum_eq];
 · apply tsum_congr; intro i; exact congr_arg (fun w:ℝ=>T (acrossT f i)*w) (Finset.prod_congr rfl fun _ _=>dilute_here ..)
 intro i h
 have hp (j:Fin r) : ∃ x:I,f x=i j:= by
    by_contra hx;apply h;change T i*(∏ j, dilute f v (i j))=0; apply mul_eq_zero_of_right;exact Finset.prod_eq_zero (mem_univ j) (dilute_miss _ _ _ hx)
 choose x hx using hp;exact ⟨x,funext hx⟩

/-- combine both mean operations -/
def collectO (K:Layer J J)(F:Orders J): Orders I:= fun e r=> crop f (draft K (F e r))
lemma collect_formula (K:Layer J J)(F:Orders J)(b:I→ℝ)(R:ℕ→ℕ): PowerSeries.map (emphasis b).toRingHom (rated R (collectO f K F)) = PowerSeries.map (emphasis (announce K (dilute f b))).toRingHom (rated R F):=by
 ext1 i
 rw [PowerSeries.coeff_map,PowerSeries.coeff_map,rated_v,rated_v]; change emphasis b _ = emphasis _ _; rw [language,language,packed,packed,map_sum,map_sum]; refine sum_congr rfl fun j _=>?_
 unfold collectO; rw [← crop_render,draft_rendered]
end YM.RegulatorIR.Diagram
