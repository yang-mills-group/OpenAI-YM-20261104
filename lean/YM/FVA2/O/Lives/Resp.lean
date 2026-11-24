import YM.FVA2.O.Lives.Continuum
/-!
# What conditions on the finite-scale MS insertion used in computing OPE?

`Response`: `Banks` conditions and global log-time evolution `helm`,
with all momenta. Ward differential `nav` raises ghost number by one and takes
responses into responses. `Certified` for also *closed* under `nav`.
Build all this on the actual `MS_Data`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Lives
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land MS.Outlook MS.Hem MS.Hem.Mell MS.Pearl Train Dock Emit
open scoped Topology ContDiff
variable {G:Gauge}{I:Type}{E:Type}{B:Deck G}{O:Booked B}{Y X X' Y': T (Glade G I)}{K:T (Flats G)}{p q:CostsM G}{t:ℤ}{η:I→ℝ}{n d:ℕ}{s:ℝ}{i:I}
variable (M : MS_Data G O)
def nav (M:MS_Data G O)(η:I→ℝ): MH ( T (Glade G I) ) := promote (both G I).J+ pairW (both G I).C ( gather M η )
def helm (M: MS_Data G O)(η:I→ℝ): MH ( T (Glade G I) ) := promote (both G I).P + pairW (both G I).X (gather M η)
lemma steers : peek (nav M η X) i s=(Φ G s).res (Pulse M (η i) s) (peek X i s):= η_res
lemma leads : peek ( helm M η X ) i s=(Φ G s).lives (Pulse M (η i) s) (peek X i s):= η_lives
lemma unitD (i:Plaid B d) : nav M η (soloV d η M i)=0:= by
    funext n u s; exact (congr_fun (steers M (i:=u) (X:=soloV d η M i)) n).trans (congr_fun (whereM M (y:=η u) (s:=s) i) n)
lemma navN (h:Banks X t): nav M η (nav M η X)=0:= by
    funext n i s; let V:=peek X i s; refine (congr_fun (steers M) n).trans ?_; rw [steers]; exact congr_fun ( square_full M (H:=V) (fun i=> (h i).invoice) (fun j=>clayS ((h j).tone i s))) n
-- Intertwining all right movements
lemma stamp_I (hp:Banks Y t) (h:∀ n,Velocity (Y n) (helm M η Y n)): Velocity (nav M η Y n) (helm M η ( nav M η Y ) n):= by
     let A:= both G I; let X:= gather M η
     let K:= helm M η Y; let H:= (A.L (Y n)+A.J (K n))+(pairW A.D X Y+pairW A.C (A.grow X) Y+pairW A.C X K) n;
     obtain hv: Velocity (nav M η Y n) H:= (Velocity.J (hp n).cross ( ((plenary (η:=η) M).lives hp) n |>.cross ) (h n)).add ( Velocity.arbor ( season M ) h n )
     suffices he : H=helm M η ( nav M η Y ) n by rw [← he]; exact hv
     funext i s; let P:=Φ G s; let V:= peek X i s; let W:=peek Y i s; let Z:= peek K i s
     have hm : (P.J (Z n)+pairW P.C V Z n)+P.L (W n)+ pairW P.D V W n+pairW P.C (P.grow V) W n=P.lives V (peek (nav M η Y) i s) n:= by
        rw [steers,show Z=(Φ G s).lives V W from leads M]; exact congr_fun ( derivative_identity M (y:=η i) (H:=W) (fun i=> (hp i).invoice) (fun j=> clayS ((hp j).tone i s))) n
     change _=peek (helm M η (nav M η Y)) i s n; rw [leads M (X:=nav M η Y)]; unfold H; simp only [Pi.add_apply]; rw [ z_pair _ _ A.D P.D (fun _ _=>rfl), z_pair _ _ A.C P.C (fun _ _=>rfl), z_pair _ _ A.C P.C (fun _ _=>rfl) ]; have hp : peek (A.grow X) i s=P.grow V:= η_grow; rw [hp]; change (P.L (W n)+P.J (Z n))+( pairW P.D V W n+pairW P.C (P.grow V) W n+pairW P.C V Z n)= P.lives V _ n; rw [← hm]; abel
structure Response (X:T (Glade G I))(M: MS_Data G O)(η:I→ℝ)(q:ℤ) : Prop where
    life : Banks X q
    vital n: Velocity (X n) (helm M η X n)
variable {M}
abbrev Certified (X:T (Glade G I))(M:MS_Data G O)(η:I→ℝ)(q:ℤ): Prop:= Response X M η q ∧ nav M η X=0
lemma Response.visit (i:Plaid B d): Response (soloV d η M i) M η 0:= ⟨markW M (M.markOK d i), comet_V M (M.markOK d i) ⟩
lemma Response.mark (h: comet d t M.bulk p K q) : Response (letIn d η K) M η t:= ⟨ markW M h, comet_V M h⟩
lemma Certified.first (i:Plaid B d): Certified (soloV d η M i) M η 0:= ⟨ Response.visit i,unitD M i⟩
lemma Response.ward (h:Response X M η t): Certified (nav M η X) M η (t+1) := ⟨ ⟨(plenary M).res h.life,fun _=> stamp_I M h.life h.vital⟩, navN M h.life⟩
lemma Response.zero : Response (0:T (Glade G I)) M η t:= ⟨fun _=> Bank.zero,by rw [map_zero]; exact fun _ _ _ _=> hasDerivAt_const ..⟩
lemma Response.add (h:Response X M η t)(hp:Response Y M η t): Response (X+Y) M η t:= ⟨ fun i=> (h.life i).add (hp.life i), by rw [map_add]; exact fun i=>Velocity.add (h.vital i) (hp.vital i) ⟩
lemma Response.sub (h:Response X M η t)(hp:Response Y M η t): Response (X-Y) M η t:= ⟨ fun i=> (h.life i).sub (hp.life i), by rw [map_sub]; exact fun i=> Velocity.sub ( h.vital i ) (hp.vital i)⟩
-- pointwise scalars commute
abbrev pay (x:I→ℂ)(X:T ( Glade G I )): T ( Glade G I ):= fun n i=> x i • X n i
lemma res_cash (x:I→ℂ): nav M η (pay x X)= pay x (nav M η X):= by
    funext n i s; change peek _ i s n=x i • peek _ i s n; rw [ steers M, steers M,show peek (pay x X) i s=x i • peek X i s from rfl ]; unfold GridR.res; rw [map_smul,map_smul,← smul_add]; rfl
lemma hel_cash (x:I→ℂ): helm M η (pay x X)= pay x (helm M η X):= by
    funext n i s; change peek _ i s n=x i • peek _ i s n; rw [leads M,leads M,show peek (pay x X) i s = x i • peek X i s from rfl]; unfold GridR.lives; rw [map_smul,map_smul, ← smul_add]; rfl
lemma Response.scale (h:Response X M η t)(x:I→ℝ): Response ( pay (fun i=> (x i:ℂ)) X ) M η t:= ⟨ fun i=> (h.life i).air x, by rw [hel_cash]; exact fun i=> (h.vital i).scale _ ⟩
lemma Response.all_fin (s:Finset E){f:E→T ( Glade G I )}(h:∀ i∈s, Response (f i) M η t): Response (∑ i∈s,f i) M η t:= by classical induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact Response.zero | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=> h j (mem_insert_of_mem hj))
end YM.FVA2.O.Lives
