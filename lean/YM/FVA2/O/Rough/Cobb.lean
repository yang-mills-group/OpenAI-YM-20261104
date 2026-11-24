import YM.FVA2.O.Knot.Picnic
import YM.FVA2.O.Hue.Filled
/-!
# Rough estimates to pass the seam (sizes only)

Don't require full derivative bounds as in `Lease`. Use the resulting
cheap (`S.full`) norm estimates e.g. in `O/Seam`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Rough
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane
open High Detect MS.Breeze
open scoped Topology ContDiff Interval
variable {E F G I J:Type}[NormedAddCommGroup E][NormedAddCommGroup F] {f h:I→ E→F}{S:Scale I}{p u:I→ E→ℝ}
-- size with allowed momentum zones (full spectrum here)
abbrev Size (T:Cost I E)(f:I→ E→ F): (I→ E→ℝ)→Prop:= T.Le (fun i x=> ‖f i x‖)
namespace Size
variable {T:Cost I E}
omit [NormedAddCommGroup E] in
lemma nonneg (h:Size T f p): T.NN p:= Cost.nn_of_le h (fun _ _ _=>norm_nonneg _)
omit [NormedAddCommGroup E] in
lemma mon (h:Size T f p)(ht:T.Le p u): Size T f u:= h.trans ht
omit [NormedAddCommGroup E] in
lemma rest (hc: T.NN p): Size T (fun _ _=> (0:F)) p:= Cost.of_le (fun i x hx=> (norm_zero (E:=F)).le.trans ( hc i x hx ))
omit [NormedAddCommGroup E] in
lemma plus (hf:Size T f p)(hp:Size T h p): Size T (fun i x=> f i x+h i x) p:= Cost.Le.left (hf.add hp (Size.nonneg hf)) (fun _ _ _=> norm_add_le ..)
omit [NormedAddCommGroup E] in
lemma minus (hf:Size T f p)(hp:Size T h p): Size T (fun i x=> f i x-h i x) p:= Cost.Le.left (hf.add hp (Size.nonneg hf)) (fun _ _ _=> norm_sub_le ..)
omit [NormedAddCommGroup E] in
lemma tally (s:Finset J){f:J→ I→ E→ F}(h:∀ i∈s,Size T (f i) p)(ht:T.NN p): Size T (fun i p=>∑ j∈s,f j i p) p:= Cost.Le.left (Cost.Le.finset_sum s (f:=fun j i x=> ‖f j i x‖) h ht) (fun _ _ _=> norm_sum_le ..)
omit [NormedAddCommGroup E] in
lemma fork {f h:I→ E→ℂ}(hf:Size T f p)(hh:Size T h u): Size T (fun i x=> f i x*h i x) (fun i x=> p i x*u i x):= Cost.Le.left (hf.mul hh (fun _ _ _=>norm_nonneg _) (fun _ _ _=>norm_nonneg _)) (fun i x _=>(norm_mul ( f i x ) ( h i x )).le)
omit [NormedAddCommGroup E] in
lemma drive {f:I→ E→ℂ}(h:Size T f p)(c:ℂ): Size T (fun i x=> c*f i x) p:= Cost.Le.left ( h.const_mul ‖c‖ (norm_nonneg _) (Size.nonneg h) ) (fun _ _ _=> ( norm_mul .. ).le ) -- h shadows
end Size
variable {α:Type}{t:I→ℝ}{P:α→ I}
variable {G:Gauge}[NormedSpace ℝ E]{A C:I→Law G}{b c:Bool}{x y:I→ℝ}{n k:ℕ}
abbrev Tax (S:Scale I)(A:I→Law G)(p:I→ℝ)(w:Wire (BH G) E QP): Prop:= Size S.full (Chart A w) (fun i _=> Qbud w S p i)
abbrev FormP (S:Scale I)(X:I→Law G)(a:I→ℝ)(c:Bool): Prop:= ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ w:Wire (BH G) E QP,fig c w.length→ Tax S X a w
abbrev Well (S:Scale I)(X:I→Law G)(a:I→ℝ)(n:ℕ) : Prop:= ∀ (E:Type)[ NormedAddCommGroup E ][ NormedSpace ℝ E ],∀ w:Wire (BH G) E QP,w.length=n→ Tax S X a w
lemma tax_size {w:Wire (BH G) E QP}(h:Cape S A x w): Tax S A x w:= h.norm_cost
lemma from_cost (h:Lease false c S A x): FormP S A x c:= fun E _ _ w hw=> tax_size ( h E w (fun i=>Bool.noConfusion i) hw )
lemma form_of (h:∀ n:ℕ,fig c n→ Well S A x n): FormP S A x c:= fun E _ _ w hv=> h w.length hv E w rfl
namespace Well
lemma takeM (h:Well S A x n) (ht:∀ i (w:Legs ( Lane4 G )),w.length=n→ C i w=A i w): Well S C x n:= by intro E _ _ w hw; rw [Tax,show Chart C w=Chart A w from funext fun i=> funext fun p=> ht i _ ( (sail_len ..).trans hw )]; exact h E w hw
lemma cram (h:FormP S A x c)(hv:fig c n): Well S A x n:= fun E _ _ w hw=>h E w (hw ▸ hv)
lemma goes (h:Well S A x n)(hp:paid S x y)(he:nn y): Well S A y n:= fun E _ _ w hw=> Size.mon (h E w hw) (by
    obtain ⟨C,hC,k,hk⟩:= paid_at ( E:=E ) hp he; refine ⟨_,hC,k,fun i p hx=>?_ ⟩; apply (mul_le_mul_of_nonneg_left (hk i p hx) (show 0≤ S.length i^pitch w from length_p ..)).trans; unfold Qbud; exact le_of_eq ( by dsimp only; ring))
lemma stays (h:Well S A x n)(hp:∀ i,x i≤y i): Well S A y n:= fun E _ _ w hw=> Size.mon (h E w hw) (Cost.of_le fun i _ _=> mul_le_mul_of_nonneg_left (hp i) (show 0≤S.length i ^ pitch w from length_p ..))
lemma unit (h:nn x): Well S (0:I→Law G) x n:= Well.cram ( from_cost ( Lease.zero (b:=false) (c:=false) h ) ) ( fun i=>Bool.noConfusion i )
lemma plus (h:Well S A x n)(hp:Well S C x n): Well S (A+C) x n:= fun E _ _ w hw=> Size.plus ( h E w hw) (hp E w hw)
lemma minus (h:Well S A x n)(hp:Well S C x n): Well S (A-C) x n:= fun E _ _ w hw=> Size.minus (h E w hw) (hp E w hw)
lemma scale (h:Well S A x n)(c:ℂ): Well S (c • A) x n:= fun E _ _ w hw=> Size.drive (h E w hw) c
lemma maskW (h:Well S A x n)(he: nn x): FormP S (fun i=> mask n (A i)) x false:= by
    apply form_of; intro r _; by_cases hv:r=n; · subst r; exact h.takeM (fun i w hn=> Book.enough _ (by exact_mod_cast hn) )
    exact ( unit he ).takeM (fun i w hw=> Book.strange _ ( by omega ))
end Well
namespace FormP
lemma part (h:FormP S A x false): FormP S A x true:= form_of (fun _ _=> Well.cram h (fun i=>Bool.noConfusion i))
lemma plus (h:FormP S A x b)(hp:FormP S C x b): FormP S (A+C) x b:= form_of (fun _ hv=> ( Well.cram h hv ).plus ( Well.cram hp hv ))
lemma minus (h:FormP S A x b)(hp:FormP S C x b) : FormP S (A-C) x b:= form_of (fun _ hv=> ( Well.cram h hv ).minus (Well.cram hp hv) )
lemma goes (h:FormP S A x b)(he:paid S x y)(ht:nn y): FormP S A y b:= form_of fun _ hv=> ( Well.cram h hv ).goes he ht
lemma stays (h:FormP S A x b)(he:∀ i,x i ≤ y i): FormP S A y b:= form_of fun _ hv=> Well.stays ( Well.cram h hv ) he
lemma scale (h:FormP S A x b)(c:ℂ): FormP S (c • A) x b:= form_of fun _ hv=> ( Well.cram h hv ).scale c
lemma unit (h:nn x): FormP S (0:I→ Law G) x b:= from_cost (Lease.zero h)
lemma pile (s: Finset J){A:J→ I→ Law G}(hp:∀ i∈s,FormP S ( A i ) x b)(hv: nn x): FormP S (∑ j∈s,A j) x b:= by
    classical induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact unit hv| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (hp i (by simp)).plus (ih fun j hj=>hp j (mem_insert_of_mem hj))
lemma chair (u:I→ QP)(hp:FormP S A x c): FormP S (fun i=>MS.Breeze.chair G ( u i ) ( A i ) ) x c:= by intro E _ _ w he; obtain h:=hp E w he; refine Cost.Le.left h (fun i p hx=>(le_of_eq (show ‖Chart _ w i p‖= ‖Chart A w i p‖ from ?_ )) ); unfold Chart; dsimp only; rw [MS.Breeze.seated,norm_mul,bill_norm,one_mul]
lemma money (u:I→ℂ)(hp:paid S (fun i=>‖u i‖) 1) (he:FormP S A x c): FormP S (fun i=> u i • A i) x c:= by
    intro E _ _ w he'; refine Size.mon (Size.fork (p:=fun i (_:E)=> (1:ℝ)) (f:=fun i _=> u i) (paid_at (E:=E) hp (fun _=>zero_le_one)) ( he E w he' )) ( Cost.of_le fun i p _=> ?_ ); simp only [one_mul]; exact le_rfl
end FormP
end YM.FVA2.O.Rough
