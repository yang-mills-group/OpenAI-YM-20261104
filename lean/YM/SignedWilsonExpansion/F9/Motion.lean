import YM.SignedWilsonExpansion.F9.Sure
import YM.SignedWilsonExpansion.F9.Ladder
/-!
# Real signed-axis naturality on the full point shelf

Character comparisons later consume basis rotations. No fixed bump equality:
Source at each site is transformed as centered germ including all power-series
orders. Partners and units are retained. `Roll` uses Wreathe without test
swap, exactly breath on physical positions; can use `seen` for coefficients.
-/
set_option autoImplicit false
set_option maxHeartbeats 760000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h b p' p d k m c N u e i j l r q:ℕ}{F:Labels.Frame G h}{H:Hol G} {Q:SectionData F}
variable {B M X Y z:ℝ}{s:Signed}{P:SourceP F}{V W:Era G ℝ}{U:Type*}
lemma eye_spin (s:Signed)(x:Volume p): eye p (spinV s _ x)=eye p x:=by
    obtain ⟨f,rfl⟩:= submitted x; rw [chronic,eye_page,thaw _ _ _ (Nat.zero_le _),Finset.univ_eq_empty,Finset.prod_empty,one_mul,s.act_zero,eye_page, Subsingleton.elim (s.perm ∘ (![]:Fin 0→Axis)) (![] : Fin 0 → Axis)]
def Roll (s:Signed)(X Y:Era G ℝ): Prop:=∀ n,rollTest (flash (Y.1 n)) (flash (X.1 n)) s 0
lemma Roll.nil (s:Signed)(G:Gauge): Roll s (0:Era G ℝ) 0:=fun n=>by intro X x a t t' hv; change train _ (flash 0)=train _ (flash 0); rw [show flash (0:PChart G n)=0 from ?_,map_zero,map_zero]; have he:= flash_mu 0 (show shellK 0 (0:PChart G n) from (silent G 0).span n); simpa using he
lemma Roll.μ (v:Roll s V W)(p:Auth k V)(q:Auth k W)(x:ℝ): Roll s (x•V) (x•W):=by
    intro n X I q' A A' g; change train _ (flash (x• W.1 n))= train _ (flash (x• V.1 n)); rw [flash_mu x (q.span _),flash_mu x (p.span _),train_smul,train_smul,v n g]
lemma Roll.sum {X Y:U→Era G ℝ} (a:Finset U)(p:∀ i∈a,Auth k (X i))(q:∀ i∈a,Auth k (Y i))(v:∀ i∈a,Roll s (X i) (Y i)): Roll s (∑ i∈a,X i) (∑ i∈a,Y i):=by
    intro n Z I q' A A' g; simp only [Prod.fst_sum,Finset.sum_apply]; rw [flash_term _ (fun i h=>(q i h).span n),flash_term _ (fun i h=>(p i h).span n),map_sum,map_sum]; exact Finset.sum_congr rfl fun i h=> v i h n g
lemma Roll.add (p:Roll s V W)(q:Auth k V)(u:Auth k W){X Y:Era G ℝ}(a: Roll s X Y)(b:Auth k X)(c:Auth k Y): Roll s (V+X) (W+Y):=by
    intro n A I t Z Z' f; change train _ (flash (W.1 n+Y.1 n))= train _ (flash (V.1 n+X.1 n)); rw [flash_add (finite_shell (u.span _)) (finite_shell (c.span _)),flash_add (finite_shell (q.span _)) (finite_shell (b.span _)),map_add,map_add,p n f,a n f]
lemma Roll.aff (p:Roll s V W)(q:Auth k V)(u:Auth k W)(c:Cost): Roll s (trim c V) (trim c W):=by
    intro n X I q' a a' g; change train _ (flash (affix c (W.1 n)))=train _ (flash (affix c (V.1 n))); rw [sponsor _ _ (u.span n), sponsor _ _ (q.span n),map_mul,map_mul,income,income,p n g]

lemma Roll.regal (x:Roll s V W)(u:m<N)(g:G.Simple)(v:LocalRatio Ñ)(hh:Auth k V)(hp:Auth k W): Roll s (verseI A Ñ m N k V) (verseI A Ñ m N k W):=by
   let t:= ll A m; let K:= A.clock.kernel; let G':=freeForms A N (m+1); let V':=freeForms A N m; let M:= roam A N m; let Y n:= (story A Ñ N (m+1)).1 (n*t.L); let R (n:Side) (P:Era G ℝ):= reed (stepAt t K n) (xree t K n) G' (M n) Ñ (Y n) k (P.1 (n*t.L)); let b:=ratioHigh A Ñ N m
   intro n; let S:=stepAt t K n; let Z:=xree t K n; have he:= (old A Ñ g v N (m+1) u).basis (n*t.L); have ht (P:Era G ℝ)(hp:Auth k P): shellK k (R n P):= reed_band _ _ _ _ k he.lamp v (hp.span _)
   change rollTest (flash (Blue.mix b (R n W))) (flash (Blue.mix b (R n V))) s 0
   refine (fun {_} _ _ _ _ H=> rollMix (A:=b) ?_ (ht _ hp) (ht _ hh) (back_cc (angle_tilt g v u)) H)
   apply reed_turn S Z G' (M n) V' he.lamp he.stem v k (hp.span _) (hh.span _) (A.blocks m 0).branches (age_sym ..) he.shape (hp.pale _) (hh.pale _) ((cond_laws A m N).1 n _ rfl) (horizon_step A m N u n _ rfl) he.valid
   rw [show S.ratio.embed 0=(0:Site (n*t.L)) from map_zero S.ratio.root]; exact x _
lemma Roll.piere (x:Roll s V W)(u:m≤ c)(v:c≤N)(g:G.Simple)(q:LocalRatio Ñ)(hh:Auth k V)(hp:Auth k W): Roll s (pier A Ñ N h k c m V) (pier A Ñ N h k c m W):=by
    induction u using Nat.decreasingInduction with
    | self=> rw [pier_top,pier_top]; exact x
    | of_succ i t ih=>
       let U:= pier A Ñ N h k c (i+1); have hr: Auth k (U V):=piered g q t v hh; have ht:Auth k (U W):=piered g q t v hp; have he:=t.trans_le v
       rw [pier_step g q t v hp,pier_step g q t v hh]; exact (Roll.μ (Roll.regal ih he g q hr ht) (Auth.verse A he g q hr) (Auth.verse A he g q ht) _)

lemma Roll.wreathe (p:Roll s V W)(q:Auth k V)(u:Auth k W)(D:ℕ) (n:Side):
    Wreathe ((tuftV (wire D) V).1 n) ((tuftV (wire D) W).1 n) s:=by
    have hx (V:Era G ℝ) (t:Volume D) : jot t ((tuftV (wire D) V).1 n)= (eye D t) • V.1 n:= funext fun i=> funext fun j=>funext fun x=> (show V.1 n i j x * eye D t= _ from mul_comm ..)
    intro c Z I x A A' H; rw [hx,hx,eye_spin]; exact p.μ q u _ n H

/-- point basis coefficient rotations across rank AND weight on all local coordinates.
 `s` acts geometrically on the test; applies the SAME intrinsic matrix to labels. -/
def mirror (F:Frame G h)(s:Signed)(d:ℕ): BankP F d →ₗ[ℝ] BankP F d where
    toFun x y:=∑ i:F.Index, bleached F s.ortho y.1 i * x (i,y.2)
    map_add' x y:=by funext; simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
    map_smul' c x := by ext1 y; rw [Pi.smul_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> mul_left_comm ..

lemma spectacle (H:Hol G)(F:Frame G h)(p:Roll s V W)(q:Auth k V)(u:Auth k W): output F d W=mirror F s d (output F d V):=by
    let D:=h+1; let v:=tuftV (wire D) V; let w:=tuftV (wire D) W; have hv:= q.tuft (wire D); have hw:= u.tuft (wire D)
    have hx i r: alliance s (v.2 i r) (w.2 i r):= solo_mercy (Auth_on hv) (Auth_on hw) s (Roll.wreathe p q u D) i r
    funext x; let X:= x.1; let i:= x.2.val; let r:= wr F X; let U:=v.2 i r; let J:= w.2 i r
    obtain ⟨a,b,ha,h'⟩:= (hv.wing i r).land; obtain ⟨c,d0,hc,hb⟩:= (hw.wing i r).land; let W':=seat F X; let Z:= notar F W'
    have he := echo_whirl F H s (show h<D from Nat.lt_succ_self _) W' U J (hx i r) h' hb ha hc ((stakes _ q _).m i r) ((stakes _ u _).m i r)
    let f (j:F.Index):= output F d V (j,x.2)
    change echoS F _ W'=∑ i, bleached F s.ortho x.1 i * f i
    change echoS F J W'= _; rw [he]
    rw [reducing F s X Z _ (weigh_cap F W') rfl W' _ (echoS F U) f]
    · rw [show Z.val=0 from rfl,hue]; simp [X]
    swap; · exact Prod.ext rfl (Subtype.ext (show _ = _ from Eq.symm (Multiset.map_zero _)))
    intro b hb hv; let v:=sheet F b; have ht:wr F v=r:= congr_arg Prod.snd hv; have hx' : b=seat F v:= Subtype.ext (Prod.ext rfl (Subtype.ext (congr_arg Subtype.val hb)))
    change echoS F _ b =echoS F (wire D ∘ V.2 i (wr F v)) (seat F v); rw [ht,hx']; rfl

-- Equivariance of solve
abbrev MotionP (F:Frame G h)(s:Signed)(P:SourceP F): Prop:= ∀ i, Roll s (P i) (∑ j:F.Index,bleached F s.ortho j i • P j)
lemma seen (H:Hol G)(F:Frame G h)(p:Roll s V W)(q:Chartage Q A Ñ m c N k u d X)(v:Auth k V)(x:Auth k W): heard F A Ñ k N p' c m W=mirror F s p' (heard F A Ñ k N p' c m V):= spectacle H F (p.piere q.length q.cap q.simple q.ratios v x) (piered q.simple q.ratios q.length q.cap v) (piered q.simple q.ratios q.length q.cap x)
lemma trim_sum (K:Finset U)(x:U→Era G ℝ)(c:Cost): trim c (∑ i∈K,x i)= ∑ i∈ K, trim c (x i):=by
    refine Prod.ext (funext fun i=>?_) ?_
    all_goals simp only [trim, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply,affix_sum]
lemma roster (v:MotionP F s P)(p:Palette F P k u d X)(x:BankP F d): Roll s (rack F P x) (rack F P (mirror F s d x)):=by
    let K:= bleached F s.ortho; let V (i:TagN F d):= auxiliary P i; let U (i:TagN F d):= ∑ j:F.Index, K j i.1 • V (j,i.2)
    have hw (i: TagN F d) : trim (PowerSeries.X^i.2.val) (∑ j, K j i.1 • P j) = U i:=by rw [trim_sum]; exact Finset.sum_congr rfl fun _ _=> trim_μ ..
    have ht i: Auth k (V i):= trim_auth _ (p.field _); have he (i: TagN F d):Auth k (U i):= Auth.sum (fun j _=> (ht _).μ _)
    have hb i: Roll s (V i) (U i):= hw i ▸ (v i.1).aff (p.field i.1) (Auth.sum (fun j _=>(p.field j).μ (K j i.1))) _
    have hx: rack F P (mirror F s d x)=∑ i,x i • U i:=by
       change ∑ i: F.Index × Fin (d+1),(∑ j,K i.1 j * x (j,i.2)) • V i= _; rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.sum_comm]
       conv_rhs=> rw [Finset.sum_comm]
       apply Finset.sum_congr rfl; intro i _; unfold U; simp_rw [Finset.smul_sum, Finset.sum_smul, mul_smul]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl (fun k _=> smul_comm ..)
    rw [hx]; unfold rack; exact Roll.sum _ (fun i _=>(ht i).μ _) (fun i _=>(he i).μ _) (fun i _=> (hb i).μ (ht i) (he i) _)
lemma solve_roll (H:Hol G)(u:Palette F P k b d X)(v:Chartage Q A Ñ m c N k b d X)(t:MotionP F s P)(x:Roll s V W)(h:Auth k V)(g:Auth k W)(D:BankP F d) : solve u v W (mirror F s d D)=mirror F s d (solve u v V D):=by
    symm; apply solve_unique u v g; let x0:=solve u v V D
    have hu:=u.mix x0; have hp:= u.mix (mirror F s d x0)
    rw [seen H F (x.add h g (roster t u x0) hu hp) v (h.add hu) (g.add hp)]; exact congr_arg _ (solve_target u v _ h)
lemma rack_sum {U:Type*} (S:Finset U)(P:SourceP F)(f:U→ℝ)(X:U→BankP F d): rack F P (∑ i∈ S,f i • X i)=∑ i∈S, f i • rack F P (X i):=by
    induction S using Finset.induction_on with
    | empty=> simp [rack]
    | @insert i S hi ih=> rw [Finset.sum_insert ‹_›, rack_plus,rack_μ, ih,Finset.sum_insert ‹_›]
-- loft linear before filtering to pure h -- can mix all rotations of the rule
lemma allCards (F:Frame G h)(s:Signed)(d:ℕ)(i:F.Index): mirror F s d (pureF F i d)=∑ j, bleached F s.ortho j i • pureF F j d:=by
    funext x; unfold mirror; simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply]; rw [Finset.sum_eq_single i]; swap; · intro b _ h; simp [pureF, Pi.single_apply,h,Ne.symm h]
    swap; · simp
    rw [Finset.sum_eq_single x.1]; swap; · intro b _ h; obtain ⟨x,y⟩:=x; simp [pureF,Pi.single_apply,h,Ne.symm h]
    swap; · simp
    obtain ⟨x,y⟩:=x; simp [pureF,Pi.single_apply]
lemma solve_linS (p:Palette F P k u d X)(v:Chartage Q A Ñ m c N k u d X)(Y:BankP F d): solve p v 0 Y=(LinearEquiv.ofBijective (lap p v) (lap_bijective p v)).symm Y:=by rw [solve,heard,pier_nil v.simple v.ratios v.length v.cap,output_nil,sub_zero]
lemma loft_price (H:Hol G)(p:Palette F P k u d X)(v:Chartage Q A Ñ m c N k u d X)(t:MotionP F s P)(i:F.Index): ∑ j, bleached F s.ortho j i • loftP p v j= mirror F s d (loftP p v i):=by
    unfold loftP; rw [←solve_roll H p v t (Roll.nil s G) (silent G k) (silent G k),allCards,solve_linS]; simp_rw [solve_linS,map_sum,map_smul]
lemma loft_seen (H:Hol G)(p:Palette F P k u d X)(v:Chartage Q A Ñ m c N k u d X)(t:MotionP F s P): MotionP F s (loft p v):=by intro i; change Roll s _ (∑ j, bleached F s.ortho j i • rack F P (loftP p v j)); rw [←rack_sum,loft_price H p v t]; exact roster t p _
end YM.WilsonCoeffUV.Mer.Xa
