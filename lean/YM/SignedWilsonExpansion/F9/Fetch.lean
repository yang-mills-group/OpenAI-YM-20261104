import YM.SignedWilsonExpansion.F9.Rack
/-!
# Boundary estimate. Test positivity not assumed. Use uniform-purchases
scale `X`; even at engineering exponent h the effect of the entry costs can
be walked back syntactically from the peer.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k m c N u e i j l r q d b:ℕ}{F:Labels.Frame G h}{H:Hol G} {Q:SectionData F}
variable {B M X Y z:ℝ}{P:SourceP F}{U:Type*}{D E W:Credit}{R:Realm G (q+1) E}

lemma charged (P:ℝ)(E:Credit)(h:1≤X) (w:0≤M):
    P*X*(E.buy X*M) ≤ (((pur P).prodC Credit.leanC).prodC E).buy X * M:=by
    rw [Credit.products,Credit.products,Credit.lean_cost]; have hx:0≤X:=zero_le_one.trans h; rw [← mul_assoc (P*X)]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal ..) hx) (zero_le_one.trans (E.purchase h))) w
lemma fix1 (h:1≤X)(p:0≤ M)(x:B≤ W.buy X*M): M+B ≤ (Credit.unit.plus W).buy X*M:=by apply le_trans (add_le_add_right x _); refine le_trans ?_ (mul_le_mul_of_nonneg_right (Credit.fuel _ _ h) p); rw [Credit.unit_cost,add_mul,one_mul]
lemma dual {c:ℝ}(h:1≤X)(p:0≤ M)(x:B ≤ W.buy X*M)(y:c≤ E.buy X*M): B+c≤ (W.plus E).buy X*M:= (add_le_add x y).trans (le_trans (le_of_eq (add_mul ..).symm) (mul_le_mul_of_nonneg_right (Credit.fuel _ _ h) p))
lemma cross {W X Y:Era G ℝ}(p:W.2 i r= X.2 i r +Y.2 i r)(a:Auth k W)(u:Auth k X)(v:Auth k Y)(j:TagIx F r): row F (Y.2 i r) j=row F (W.2 i r) j-row F (X.2 i r) j:= by rw [p,← show (X+Y).2 i r=X.2 i r+Y.2 i r from rfl,axPlus u v]; ring
lemma positiveC (h:1≤X)(E:Credit):0≤E.buy X:= zero_le_one.trans (E.purchase h)
lemma wake {c:Credit}(h:1≤X)(p:0≤ M) : 0≤ c.buy X*M:= mul_nonneg (positiveC h _) p
-- core same-rank residual bound, only uses terminal row and predecessor ranks
lemma register (F:Frame G h)(e r p u k:ℕ)(hz:e≤p)(hy:Ample h u r)(E W:Credit): ∃ C: Credit,∀ X≥(1:ℝ), ∀ M≥(0:ℝ), ∀ (P:SourceP F)(x:BankP F p), Palette F P k u p X → ∀ (Y:Era G ℝ)(_ :Auth k Y), Fruit 0 1 u (Y.2 e r) M→
    (∀ i∈part F e r p,‖x i‖ ≤ E.buy X*M) → (∀ i:TagIx F r, ‖row F ((Y+rack F P x).2 e r) i‖≤ W.buy X*M) →
    (∀ i:TagIx F r, ‖x (eyeTag F e p hz i)‖≤ C.buy X*M) ∧ Fruit 0 1 u ((Y+rack F P x).2 e r) (C.buy X*M):=by
    let A:ℝ:=Fintype.card (TagN F p); let K:= pur (rowCost F u r); let T:= Credit.unit.plus (((pur A).prodC Credit.leanC).prodC E); let a:ℝ:= Fintype.card (TagIx F r); let τ:= TagIx F r
    obtain ⟨Z,H⟩:= oneRow (fun i:τ=>wT F i) (h+1) (fun i=>Nat.lt_succ_of_le (F.bound i)) (W.plus (K.prodC T)) (K.prodC Credit.leanC)
    let D:=T.plus (((pur a).prodC Credit.leanC).prodC Z); let C:= Z.plus D
    refine ⟨C,fun X hx M hM P x v Y hY hv q x'=>?_⟩; let V:=before F P x e r; let p':= Y+V; let U:=sliceP F P x e r hz; let Q:=Y+rack F P x
    have hh:Fintype.card (TagN F p)≥0:=Nat.zero_le _
    have ht0:p'.2 e r=Y.2 e r+V.2 e r:=rfl
    have ht : Q.2 e r=p'.2 e r+U.2 e r:= by change _+(rack F P x).2 e r= _; rw [v.slim hz x, ←add_assoc]; rfl
    have hK:Fruit 0 1 u (p'.2 e r) (T.buy X*M):= (hv.plus (v.charger x hz q (wake hx hM)) zero_le_one).more (fix1 hx hM (charged A E hx hM)); let S:= typus F P r
    have hS:= v.licensed (r:=r) hy; have hs: rowCost F u r * X ≤ (K.prodC Credit.leanC).buy X:= by rw [Credit.products,Credit.lean_cost]; exact mul_le_mul_of_nonneg_right (pure_goal _ X) (zero_le_one.trans hx)
    have hf (i:τ) :‖(S *ᵥ paper x e hz) i‖≤ (W.plus (K.prodC T)).buy X*M:=by rw [show (S*ᵥ _) i= _ from Eq.symm (v.price x hz i),cross ht (hY.add (v.mix x)) (hY.add (v.lacuna x)) (v.slice hz x)]; refine (norm_sub_le ..).trans (dual hx hM (x' i) ((row_bound F _ hK hy.floor i).trans ?_)); rw [Credit.products, mul_assoc]; exact mul_le_mul_of_nonneg_right (pure_goal _ X) (wake hx hM)
    have hy (i:τ): ‖x (eyeTag F e p hz i)‖≤ Z.buy X*M:= H X hx M hM S _ ⟨hS.self,fun i j=>(hS.value i j).trans hs,hS.ties⟩ hf i
    refine ⟨fun i=> (hy i).trans (mul_le_mul_of_nonneg_right (Credit.thickens _ hx) hM),?_⟩; change Fruit 0 1 u (Q.2 e r) _; rw [ht]; exact (hK.plus (v.sliceFee x hz hy) zero_le_one).more ((dual hx hM le_rfl (charged a Z hx hM)).trans (mul_le_mul_of_nonneg_right (Credit.thickened _ hx) hM))

-- Full recursion; accepts prices on just a prefix of e increasing r decreasing.
abbrev When (e' r' e r:ℕ):Prop:= e'< e ∨ e'=e∧r≤r'
lemma When.back {e' r':ℕ} (p:When e' r' e r)(g:lowerGrade i j e' r'): When i j e r:=by unfold When at *; unfold lowerGrade at g; omega

def Travels (F:Frame G h)(p k u i r:ℕ)(D:Credit):Prop:= ∀ Q:SectionData F,∀ (A:Levels G)(Ñ:ChartRatio G)(m c N:ℕ)(M X:ℝ)(P:SourceP F)(Y:Era G ℝ) (x:BankP F p)(e r':ℕ), e≤p→When i r e r'→0≤ M →Palette F P k u p X → Auth k Y → Chartage Q A Ñ m c N k u p X →
    (∀ i j, When i j e r'→Fruit 0 1 u (Y.2 i j) M) →
    (∀ i j, When i j e r'→ ∀ v:TagIx F j, ‖row F ((pier A Ñ N h k c m (Y+rack F P x)).2 i j) v‖≤ M) →
    (∀ j,m ≤ j → j≤c → Fruit 0 1 u ((pier A Ñ N h k c j (Y+rack F P x)).2 i r) (D.buy X*M)) ∧ (∀ g:i≤p,∀ v:TagIx F r, ‖paper x i g v‖≤ D.buy X*M)
lemma Travels.more (p:Travels F q k u i r D)(v:∀ X:ℝ,1≤ X→ D.buy X≤ W.buy X): Travels F q k u i r W:=by
    intro Q A Ñ m c N M X P Y x e r' hp hr hM t g hx q f; have ht:= mul_le_mul_of_nonneg_right (v X hx.pos) hM; obtain ⟨h1,h2⟩:= p Q A Ñ m c N M X P Y x e r' hp hr hM t g hx q f; exact ⟨fun _ a b=> (h1 _ a b).more ht,fun a w=> (h2 a w).trans ht⟩
lemma wardOff (hp:k+i<r):Travels F p k u i r W:=by
    intro Q A Ñ m c N M X P Y x e r' he hr hx w v t hK hf; constructor
    · intro j h a; rw [(piered t.simple t.ratios a t.cap (v.add (w.mix x))).coverN i r hp]; exact Fruit.zero.more (wake t.pos hx)
    intro _ i; have hp':= (fitsRank F i).trans t.order; omega
lemma enlightens (F:Frame G h) (p k u i r:ℕ)(he:i≤p)(v:r≤ k+i)(E:Credit)(H:∀ i' j, lowerGrade i' j i r → Travels F p k u i' j E): ∃ W:Credit, Travels F p k u i r W:=by
    by_cases hx: Ample h u (k+p); swap; · exact ⟨Credit.unit,fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t=>False.elim (hx t.ample)⟩
    have hu:r≤k+p:=by omega
    obtain ⟨B,f⟩:= priceBack F r E Credit.unit; obtain ⟨D,g⟩:= register F i r p u k he (hx.more hu) E B; obtain ⟨Z,w⟩:= ferry F E B D
    refine ⟨D.plus Z,fun Q A Ñ m c N M X P Y x e r' hz r0 hM t hY q f0 g0=>?_⟩; let P':=Y+rack F P x; have hP:= hY.add (t.mix x); let C:= P'; let V j:=pier A Ñ N h k c j P'
    have h j (h:m≤ j)(hi:j≤ c): Earlier (V j) i r u (E.buy X*M):= fun a x0 v=> (H a x0 v Q A Ñ m c N M X P Y x e r' hz (r0.back v) hM t hY q f0 g0).1 _ h hi
    have hK(i0:TagIx F r): ‖row F ((V m).2 i r) i0‖≤ Credit.unit.buy X*M:=by rw [Credit.unit_cost,one_mul]; exact g0 _ _ r0 i0
    have ha j (hd:m≤ j)(hx:j≤ c) i₀ : ‖row F ((V j).2 i r) i₀‖≤ B.buy X*M:= f Q A Ñ k u p m c N X M q.pos hM i he hu q P' hP h hK i₀ j hd hx
    have hb i₀: ‖row F (P'.2 i r) i₀‖≤ B.buy X*M:=by have hp:=ha c q.length le_rfl i₀; unfold V at hp; rwa [pier_top] at hp
    have hp : ∀ i₀∈ part F i r p, ‖x i₀‖ ≤ E.buy X*M:=by
       rintro ⟨x',k⟩ hk; have hv:= (Finset.mem_filter.mp hk).2; exact (H k.val (wr F x') hv Q A Ñ m c N M X P Y x e r' hz (r0.back hv) hM t hY q f0 g0).2 (Nat.le_of_lt_succ k.isLt) ⟨x',rfl⟩
    obtain ⟨hX,hD⟩:= g X q.pos M hM P x t Y hY (f0 _ _ r0) hp hb; refine ⟨fun j hp hi=>?_,fun _ v=> (hX v).trans (mul_le_mul_of_nonneg_right (Credit.thickens _ q.pos) hM)⟩; exact (w Q A Ñ k u p m c N X M q.pos hM i r he hu q P' hP h ha hD j hp hi).more (mul_le_mul_of_nonneg_right (Credit.thickened _ q.pos) hM)
-- Uniform order certificate includes the orientation precision (any rank cutoff with previous powers)
lemma billed (F:Frame G h)(p u k:ℕ): ∃ W:Credit,∀ i≤p,∀ r, Travels F p k u i r W:=by
    refine seasonsPaid (fun i r W=> Travels F p k u i r W) k p ?_ (fun _ _ h _=>wardOff h) (fun i r A B x w=>w.more x)
    intro i a b Y h; by_cases v:b≤k+i; exact enlightens F p k u i b a v Y h; exact ⟨Y,wardOff (by omega)⟩
end YM.WilsonCoeffUV.Mer.Xa
