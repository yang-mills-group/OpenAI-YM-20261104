import YM.WilsonCoeffUV.Root.Post.March
/-!
# Primary column graphs. Constructors only run at levels with matching Loom; theorem applies there.
Offsets rooted at each scale. Fields not vacuum closures. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a N m:ℕ} {G:Gauge}{F:Labels.Frame G h}

abbrev Island (F:Frame G h) (D) := PatchPanel F D × Thesis F D
structure Shimmer (P:Island F D): Prop where
   scan: Chain F P.1 P.2
   era: prismata F P.2=1

lemma epoch {P:Island F D}(h: Shimmer P)(i):∀ e, Symbol F i (P.2 i) e:=by
   intro e j; rw [← coined P.2 e j i,h.era]; unfold lineS; rw [Matrix.of_apply]
   by_cases t:j=i; · subst j; by_cases b:e=0 <;> simp [b]
   rw [Matrix.one_apply_ne t, map_zero,if_neg (fun ⟨_,v⟩=>t v.symm)]
lemma affirm (X:PatchPanel F D)(Y:Thesis F D)(p:Chain F X Y)(i): Stakes (Y i):=⟨solo_pure (p.solo i),solo_upright (p.solo i),fun _ _=> solo_mural (p.solo _) _ _⟩
lemma streams {P:Island F D}(p:Shimmer P)(i): Lit F i (P.2 i):= ⟨solo_shape (p.scan.solo _),affirm _ _ p.scan _,epoch p i 0⟩
lemma freshly (T:SectionData F)(H:Hol G)(e:h<D)(p:T.Sound H)(b:Bid.pop T) : Shimmer ((fun n i=>herald T e i n),anthem T e):=by
   have ht s n i:Wreathe (herald T e i n) (impose (fun j=> herald T e j n) (paintC F s) i) s:= by rw [canvasF]; exact herald_wind T e i s n b H p
   refine ⟨⟨fun i=>⟨herald_job T e i, herald_norm T e i, herald_auth T e i,fun n=>?_⟩,ht⟩,extortion (fun k i j=>?_)⟩
   · have he:=ht 1 n i; rw [blank, impose_plain] at he; exact he
   rw [coined]; change glean F (anthem T e j) k i=lineS 1 k i j; rw [cornerRead T e _ _ H p b]; by_cases hv:i=j; · subst j; by_cases v:k=0 <;> simp [lineS,v]
   simp [lineS,hv]

variable (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(w:h<D)
include w
-- coding Y, transactions without semantic precheck, zero outside range allowed
omit w in
def descend (N m:ℕ)(Y:Island F D): Island F D := ((fun n i=> cloakP A Ñ N m h n (Y.1 (n*(ll A m).L) i)),fun i=> marchT A Ñ N m h (Y.2 i))
omit w in
def imprint (Y:Island F D)(u: Coil F): Island F D:= (fun n=> impose (Y.1 n) u,impose Y.2 u)
omit w in
def reglazed (Y:Island F D): Island F D:= imprint Y ((prismata F Y.2)⁻¹)

noncomputable def Peaks (N m:ℕ):Island F D:= if _h:m<N then reglazed (descend A Ñ N m (Peaks N (m+1))) else (fun n i=>herald T w i n,anthem T w)
termination_by N-m
lemma Peak_initial (N): Peaks A Ñ T w N N=(fun n i=>herald T w i n, anthem T w):=by rw [Peaks,dif_neg (lt_irrefl _)]
lemma marched (t:m<N): Peaks A Ñ T w N m=reglazed (descend A Ñ N m (Peaks A Ñ T w N (m+1))):=by rw [Peaks,dif_pos t]
omit T
omit w in
lemma refluent {V:Island F D}(p:IsUnit (prismata F V.2).det): impose (reglazed V).2 (prismata F V.2)=V.2:=by unfold reglazed imprint; dsimp only; rw [imposition,nonsing_inv_mul _ p,impose_plain]
omit w in
lemma irComm {n:Type*}[Fintype n][DecidableEq n]{E:Type*}[CommRing E](R T: Matrix n n E)(p:IsUnit R.det)(h:R*T=T*R): R⁻¹*T=T*R⁻¹:=by
   calc _ = R⁻¹*(T*R)*R⁻¹ :=by simp only [←Matrix.mul_assoc R⁻¹ T R, Matrix.mul_assoc (R⁻¹*T),Matrix.mul_nonsing_inv _ p,_root_.mul_one]
        _ = T*R⁻¹:= by rw [←h,← Matrix.mul_assoc R⁻¹ R T,nonsing_inv_mul _ p, _root_.one_mul]
-- Stipulated Usage sync
omit w in
lemma byPath (p:m<N)(g:G.Simple)(h':LocalRatio Ñ)(V:Island F D) (W:Usage A Ñ m)(I:Cloister G h)(e:inkPin I=W.gear) (R: Stand (inkPin I)) (u:HEq R (W.postStand p g h')): (descend A Ñ N m V).2 = fun i=> fanfare (inkPin I) R h (V.2 i):=by
   have he (K:Gear G)(v:Stand K)(s:K=W.gear)(u:HEq v (W.postStand p g h')): (descend A Ñ N m V).2=fun i=>fanfare K v h (V.2 i):=by subst K; rw [eq_of_heq u]; rfl
   exact he _ _ e u
lemma path_warp (p:m<N)(g:G.Simple)(h':LocalRatio Ñ)(H:Hol G)(V:Island F D)(u:Shimmer V)(I:Cloister G h)(W:Usage A Ñ m)(e:inkPin I=W.gear) (R:Stand (inkPin I))(v:HEq R (W.postStand p g h')) (T:Courant I R) :
    let T:=prismata F (descend A Ñ N m V).2
    leaseM ((inkPin I).patch.L) F (lineS T 0) ∧ Shimmer (reglazed (descend A Ñ N m V)):=by
    intro P; let Y:=descend A Ñ N m V
    have hx: Chain F Y.1 Y.2:= running A Ñ p g h' u.scan
    have hg:= billing F Y.2 (fun i=>solo_shape (hx.solo i))
    have hE:= byPath A Ñ p g h' V W I e R v
    have hv : leaseM (inkPin I).patch.L F (lineS P 0):=by
       refine ⟨hg 0,fun i j t x=>?_⟩; unfold P; rw [coined,hE]
       have he: Stakes (fanfare (inkPin I) R h (V.2 j)):= by
          have ht:= affirm Y.1 (descend A Ñ N m V).2 hx j; rw [hE] at ht; exact ht
       have Hq :dragCup Bank.terrain I.lamp.s I.lamp.path.D R.Q:=by
          apply dragCup.mono (σ:=I.lamp.path.s) ?_ (I.lamp.outlet.trans I.lamp.path.holds.le)
          have hc (J:Gear G)(p':Stand J)(hq:W.gear=J)(hx:HEq p' (W.postStand p g h')): dragCup Bank.terrain J.s J.D p'.Q:= by subst J; rw [eq_of_heq hx]; exact ((W.cardG.shift N N N p (le_refl _) (le_refl _)).1.oneP)
          exact hc _ _ e.symm v
       obtain ⟨s,X,a,b⟩:= solo_stretch (u.scan.solo j) 0 (valence F j); exact streak T H w (streams u j) Hq a b he i t x
    have ha:= hx.commutes _ _ H w
    let Q:= reglazed Y; have hc:=stellarized hv; have hf:= tiller hv hg
    refine ⟨hv, ?co,?_⟩
    case co=> apply Chain.pierce Y.1 Y.2 hx hf; intro s; exact Eq.symm (irComm _ _ hc (ha s).symm)
    change prismata F (impose Y.2 P⁻¹)=1; rw [prismata_bind F _ (fun i=> solo_stretch (hx.solo i))]; exact Matrix.mul_nonsing_inv P hc
end YM.WilsonCoeffUV.Cosmos
