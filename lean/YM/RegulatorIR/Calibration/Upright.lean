import YM.RegulatorIR.Calibration.Spring

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Calibration
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {X:Type}{M:X→ℕ}{n: Page M → Side}
-- predecessor be
private def wh (i j:Page M):Prop:= i.bindW=j.bindW∧i.downW ≤ j.downW
private lemma wh_r (i:Page M):wh i i:=⟨rfl,le_refl _⟩
private lemma wh_t {i j k:Page M}(h:wh i j)(ht:wh j k):wh i k:= ⟨h.1.trans ht.1,h.2.trans ht.2⟩
private lemma wh_o (i:Flap M): wh i.prev i.next:= ⟨rfl,Nat.le_succ _⟩
private lemma wh_fin (i:Page M) (x:X) (h:i.bindW=x): wh i (Page.finallyW M x):= ⟨h,i.good.trans (by rw [h];exact le_rfl)⟩
private lemma wh_eq {i j:Page M}(h:i.bindW=j.bindW)(hv:i.downW=j.downW):i=j:= by cases i;cases j;congr
section Tempo
variable (S:Circuit M n){K:KernelChoices} (Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G)(c:G.ColorIndex)
local notation "Q"=> S.payroll Y G Z
variable (s:Page M→Scale){t:Page M→Scale}{x:X}{p e:ℕ}
private lemma comms (a:Page M) (h:∀ i:Page M,wh i a→ Squares e (tale (s i).beta) (tale (t i).beta)): Matches e ((Q s).bulk a) ((Q t).bulk a):=by
 refine Page.proves (g:= fun a=>(∀ j,wh j a→ Squares e (tale (s j).beta) (tale (t j).beta)) → Matches e ((Q s).bulk a) ((Q t).bulk a)) ?_ ?_ a h -- infer family
 · intro w B; apply fenestra S Y G Z s w; exact B _ (wh_r _)
 intro w ih ht; exact winding S Y G Z s w (ht _ (wh_o w)) (ih (fun i h=> ht i (wh_t h (wh_o w))))
def Tuned (e:ℕ)(i:Page M):Prop:= ∀ j≤e, 0<j→ Rules.token ((Q s).bulk i j 2) c=biases (s i) j
def Known (p:ℕ) : Prop:= ∀ i:Page M,Tuned S Y G Z c s p i∧Seconds (s i) p
private lemma tuned_edit (k:Page M)(h:Tuned S Y G Z c s p k)(ht:Squares p (tale (s k).beta) (tale (t k).beta))(hp:Matches p ((Q s).bulk k) ((Q t).bulk k)): Tuned S Y G Z c t p k:=by
 intro i hi H; rw [← hp i hi, show biases (t k) i=biases _ _ from (ht i hi).symm]; exact h i hi H
private lemma seconds_v {s t: Scale}(h: Squares p (tale s.beta) (tale t.beta))(he:Seconds s p) : Seconds t p := fun i hi h' => (h i hi).symm.trans (he i hi h')
private lemma slips (f:Flap M){i:Page M} (h:wh i f.next)(hh:i≠ f.next): wh i f.prev:=by
 refine ⟨h.1,?_⟩; have ht:i.downW ≠ f.next.downW:=fun hp=>hh (wh_eq h.1 hp); have hp:= h.2; have hr:f.next.downW=f.prev.downW+1:=rfl;omega
private lemma tilts' (a:Page M) (h:∀ i,wh i a→ Seconds (s i) e): Steady ((Q s).bulk a) e:=by
 refine Page.proves (g:=fun a=>(∀ i,wh i a→ Seconds (s i) e)→ Steady ((Q s).bulk a) e) ?_ ?_ a h
 · intro w H; exact steadyW _ _ _ _ _ _ (H _ (wh_r _))
 intro w ih H; exact steadyS _ _ _ _ _ w (H _ (wh_o _)) (ih fun i h=> H _ (wh_t h (wh_o w)))
-- each stage possible with feeds realizing positivity
abbrev Tent {X:Type}(M:X→ℕ):= Page M→Feeds
def sheet (H:Tent M): Page M→Scale:= Feeds.scale ∘ H
local notation "TunedP"=> Tuned S Y G Z c
private lemma fileUp (v:Feeds)(h:Seconds v.scale e)(k:ℝ)(hp:(e+1)%2=1→k=0):∃ t:Feeds, biases t.scale (e+1)=k ∧Seconds t.scale (e+1)∧Squares e (tale t.scale.beta) (tale v.scale.beta) :=by
 obtain ⟨t,H,hK⟩:=step_feed v e (k-biases v.scale (e+1)); have he: biases t.scale (e+1)=k:= hK.trans (by abel)
 refine ⟨t,he,fun i hi hi'=>?_,H⟩; by_cases hv:i=e+1;subst i; rw [he,hp hi'];exact seconds_v (fun i hi=> (H i hi).symm) h i (by omega) hi'
private lemma wh_j (x:X)(i:Page M)(h:wh i (Page.opening M x)) : i=Page.opening M x:= wh_eq h.1 (le_antisymm h.2 (Nat.zero_le _))
-- remains page-by-page through e+1 before pivot constraint.
def Protect (x:X)(p:ℕ)(t:Tent M):Prop:=∀ i:Page M,i.bindW=x→ TunedP (sheet t) p i ∧ Seconds (sheet t i) p
private def Part (q:Page M)(p:ℕ) (t T: Tent M):Prop:= ∀ i:Page M,i.bindW=q.bindW→ Squares p (tale (sheet T i|>.beta)) (tale (sheet t i|>.beta))∧ TunedP (sheet T) p i ∧ Seconds (sheet T i) p ∧ (wh i q → TunedP (sheet T) (p+1) i∧Seconds (sheet T i) (p+1))
-- preserving representation using only tale through p steps
private lemma doc (a b:Tent M) (e:ℕ) (H:Protect S Y G Z c x e a)(hp:∀ i:Page M,i.bindW=x→ Squares e (tale (sheet b i|>.beta)) (tale (sheet a i|>.beta))) : Protect S Y G Z c x e b:=by
 intro i hi; have hv:Matches e ((Q (sheet b)).bulk i) ((Q (sheet a)).bulk i):= comms _ _ _ _ _ _ (fun j h=> hp j (h.1.trans hi))
 exact ⟨ (tuned_edit _ _ _ _ _ _ _ (H i hi).1 (fun j hj=> (hp i hi j hj).symm) (fun j hj=>(hv j hj).symm)), seconds_v (fun j hj=> (hp i hi j hj).symm) (H i hi).2 ⟩
private lemma fields_v (t:Tent M) : ∀ i:Page M,Protect S Y G Z c i.bindW e t→ ∃ V:Tent M, Part S Y G Z c i e t V:=by
 refine Page.proves ?_ ?_
 · intro w h; let a:=Page.opening M w; let U:=sheet t
   obtain ⟨p,hp,hH,hr⟩:= fileUp (t a) (e:=e) ((h a rfl).2) 0 fun _=>rfl
   let V:= Function.update t a p
   have He:sheet V a=p.scale:= by change (Function.update t a p a).scale=p.scale;rw [Function.update_self]
   have hx(i:Page M) (_:i.bindW=a.bindW): Squares e (tale (sheet V i|>.beta)) (tale (sheet t i|>.beta)):=by
      by_cases H:i=a;subst i;rw [He];exact hr
      rw [show sheet V i= _ from congr_arg Feeds.scale (show V i=t i from Function.update_of_ne H ..)]; exact fun _ _=>rfl
   have hf:=doc S Y G Z c t V e h hx
   refine ⟨V,fun i hi=>⟨hx i hi,(hf i hi).1,(hf i hi).2,fun ht=>?_⟩⟩
   rw [wh_j w i ht,show Page.opening M w=a from rfl]; exact ⟨fun _ _ H=> stamps _ _ _ _ _ w _ H c, He ▸ hH⟩
 intro f ih h; obtain ⟨b,hb⟩:=ih h; let i:= f.next; let s:=sheet b; let B:= Q s
 let k:= Rules.token (B.bulk i (e+1) 2) c; have hx:=hb i rfl
 have HE : Steady (B.bulk i) (e+1):=by
    apply steadyS S Y G Z (s:=s) f (hb f.prev rfl|>.2.2.2 (wh_r _)|>.2)
    exact tilts' _ _ _ _ _ _ fun w hp=> (hb w hp.1).2.2.2 hp|>.2
 have Hk: (e+1)%2=1→k=0:=by
    intro h;have hp:B.bulk i (e+1) 2=0:= Classical.not_not.mp (fun h'=> by have hp:= HE (e+1) le_rfl 2 h';omega)
    unfold k;rw [hp]; unfold Rules.token Pupil.shine Momentum.recital; simp_rw [show ∀ i j:CapG G, ∀ p,starE 0 i j p=(0:ℝ) from fun _ _ _=>rfl];simp
 obtain ⟨m,hm,hM,H⟩:= fileUp (b i) hx.2.2.1 k Hk
 let V:=Function.update b i m;let u:=sheet V
 have hV:u i=m.scale:=congr_arg Feeds.scale (Function.update_self ..)
 have hu(j:Page M)(hh:j≠i):u j=s j:=congr_arg Feeds.scale (Function.update_of_ne hh ..)
 have hz(w:Page M)(hw:w.bindW=i.bindW) :Squares e (tale (u w|>.beta)) (tale (sheet t w|>.beta)) :=by
    intro k hk; by_cases hi:w=i; subst w;rw [hV]; exact (H k hk).trans (hx.1 k hk)
    rw [hu w hi]; exact hb w hw|>.1 k hk
 have hE:=doc S Y G Z c t V e h hz
 have hT(w:Page M)(ht:wh w f.prev):w≠i:=fun hf=> by
    rw [hf] at ht; have h:= ht.2; change f.offset+1≤ f.offset at h;omega
 have hs(w:Page M)(ht:wh w f.prev): Matches (e+1) ((Q u).bulk w) (B.bulk w):= comms _ _ _ _ _ w (fun w' hi=> by
    rw [hu w' (hT _ (wh_t hi ht))];exact fun _ _=>rfl)
 refine ⟨V,fun w hw=>⟨hz w hw,(hE w hw).1,(hE w hw).2,fun ht=>?_⟩⟩
 change TunedP u _ w ∧ Seconds (u w) _; by_cases hh:w=i
 · subst w; have H':Matches (e+1) ((Q u).bulk i) (B.bulk i):= winding S Y G Z u f (t:=s) (by rw [hu f.prev (hT _ (wh_r _))];exact fun _ _=>rfl) (hs f.prev (wh_r _))
   refine ⟨?_,hV ▸ hM⟩; intro j hj he; by_cases hk:j=e+1; subst j; rw [H' (e+1) le_rfl, hV]; exact hm.symm
   exact (hE i hw).1 j (by omega) he
 have hq:= slips f ht hh; obtain ⟨hp,ht⟩:= (hb w hw).2.2.2 hq; refine ⟨fun j hj he=>?_,hu w hh ▸ ht⟩
 rw [hs w hq j hj,hu w hh]; exact hp j hj he
lemma bulk_comms (i:Page M)(h:∀ j:Page M,j.bindW=i.bindW→Squares e (tale (s j|>.beta)) (tale (t j|>.beta))): Matches e ((Q s).bulk i) ((Q t).bulk i):= comms S Y G Z s i (fun j hi=>h j hi.1)
lemma all_protect (a b:Tent M) (e:ℕ) (H:Protect S Y G Z c x e a)(hp:∀ i:Page M,i.bindW=x→ Squares e (tale (sheet b i|>.beta)) (tale (sheet a i|>.beta))) : Protect S Y G Z c x e b:= doc _ _ _ _ _ _ _ _ H hp
-- at current readings **not** requiring the final contour.
lemma forecast (w:X)(t:Tent M) (h:Protect S Y G Z c w e t):∃ V:Tent M, (∀ p:Page M,p.bindW=w→Squares e (tale (sheet V p|>.beta)) (tale (sheet t p|>.beta))) ∧ Protect S Y G Z c w (e+1) V:=by
 obtain ⟨V,H⟩:= fields_v S Y G Z c t (Page.finallyW _ w) h; exact ⟨V,fun p hp=>(H p hp).1, fun p hp=>(H p hp).2.2.2 (wh_fin p w hp)⟩
lemma spinC (w:X)(V:Tent M) (s:Tent M) (D:Choice M) (hv: Protect S Y G Z c w (e+1) V)(hp: (∀ p:Page M,p.bindW=w→Squares e (tale (sheet V p|>.beta)) (tale (sheet s p|>.beta)))) (hk:s (D.choose w)=dawn):∃ b:Tent M, (∀ p:Page M,p.bindW=w→ Squares e (tale (sheet b p|>.beta)) (tale (sheet V p|>.beta))) ∧ Protect S Y G Z c w (e+1) b ∧ b (D.choose w)=dawn:=by
 let k:=D.choose w;let U:=sheet V; let v:= -(biases (U k) (e+1))
 choose t ht using (fun i:Page M=>step_feed (V i) e v)
 let a: Tent M:= Function.update t k dawn;have hr:a k=dawn:= Function.update_self ..
 have ht'(i:Page M) : Squares e (tale (sheet a i|>.beta)) (tale (sheet V i|>.beta)) ∧ biases (sheet a i) (e+1)=biases (sheet V i) (e+1)+v:=by
    by_cases he:i=k
    · subst i; have h₀:sheet a k=dawn.scale:=congr_arg Feeds.scale hr; rw [h₀,starts]; refine ⟨fun i hi=> ?_,(add_neg_cancel _).symm⟩
      have hs:= hp k rfl i hi;rw [show sheet s k= dawn.scale from congr_arg Feeds.scale hk] at hs; exact hs.symm
    have H:sheet a i=(t i).scale:=congr_arg Feeds.scale (Function.update_of_ne he ..);rw [H];exact ht i
 let δ(i:Page M):= (sheet a i)
 have hh(i:Page M): Matches e ((Q (sheet a)).bulk i) ((Q (sheet V)).bulk i):= bulk_comms S Y G Z _ i fun j _ => (ht' j).1
 have hx:∀ i:Page M,(Q (sheet a)).bulk i (e+1)= (Q (sheet V)).bulk i (e+1)+Warm.peak (v • coil (S.scroll_j Y G i)):= Page.proves (fun j=> top_h S Y G Z _ j (ht' _).2 (ht' _).1) (fun f h=> chests S Y G Z _ f (ht' _).2 (ht' _).1 (hh f.prev) h)
 refine ⟨a,fun p _=>(ht' p).1,fun p hi=>?_,hr⟩; obtain ⟨Ht,hQ⟩:=hv p hi
 have hf:= increases S Y G Z _ c p (hx p)
 refine ⟨fun j hj he=>?_,fun j hj hJ=>?_⟩
 · by_cases h:j=e+1
   · subst j; rw [hf,(ht' p).2,Ht (e+1) le_rfl (by omega)]
   rw [hh p j (by omega),show biases (sheet a p) j= _ from (ht' p).1 j (by omega)]; exact Ht j hj he
 by_cases h:j=e+1
 · subst j; rw [(ht' p).2,hQ _ le_rfl hJ,show v= _ from rfl];change _+ -(biases (U k) (e+1))= _;rw [show biases (U k) (e+1)=0 from (hv k rfl).2 _ le_rfl hJ]; simp
 rw [show biases ..= _ from (ht' p).1 j (by omega)]; exact hQ j hj hJ
-- exists at all fixed finite order with reference fixed. no work or hG demanded here.
structure Notebook (D:Choice M)(T:Tent M)(p:ℕ):Prop where
 clean : Known S Y G Z c (sheet T) p
 reference (i:X): T (D.choose i)=dawn
lemma promotes (w:X) (D:Choice M)(H:Tent M) (h:Protect S Y G Z c w p H)(ht:H (D.choose w)=dawn):∃ U:Tent M, (∀ i:Page M,i.bindW=w→Squares p (tale (sheet U i|>.beta)) (tale (sheet H i|>.beta))) ∧ Protect S Y G Z c w (p+1) U∧ U (D.choose w)=dawn:=by
 obtain ⟨V,hv,hP⟩:= forecast _ _ _ _ _ _ _ h; obtain ⟨U,hU,Hq,Hv⟩:= spinC S Y G Z c w V H D hP hv ht; exact ⟨U,fun i hi j hj=> (hU i hi j hj).trans (hv i hi j hj),Hq,Hv⟩
lemma tomorrows (D:Choice M)(p:ℕ) : ∃ T:Tent M, Notebook S Y G Z c D T p:=by
 induction p with
 | zero=>
    refine ⟨fun _=>dawn,⟨fun i=>?_,fun i=>rfl⟩⟩; exact ⟨fun j hj he=>False.elim (by omega),start_at⟩
 | succ p ih=>
    obtain ⟨t,H⟩:=ih; choose b hb using (fun w=> promotes (p:=p) S Y G Z c w D t (fun i _=> H.clean i) (H.reference w));let f(p:Page M):= b p.bindW p
    refine ⟨f,⟨fun i=>doc S Y G Z c (b i.bindW) f _ (hb i.bindW).2.1 ?_ i rfl, fun i=>(hb i).2.2⟩⟩
    intro p hp; rw [show sheet f p= _ from congr_arg Feeds.scale (show f p=b i.bindW p from by unfold f;rw [hp])];exact fun _ _=>rfl
end Tempo
end YM.RegulatorIR.Calibration
