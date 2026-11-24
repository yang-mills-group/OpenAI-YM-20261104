import YM.SignedWilsonExpansion.F9.MergeSouth
/-!
# Resume bulk price before stop comparing all reporter faces

Preserve relative units. Couple same cutoff kernel.Force covariance join suppresses
error even through scoped normalize. Take long budget.
-/
set_option autoImplicit false
set_option maxHeartbeats 880000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r p u n :ℕ}
variable {B Q D Z X Y η t a ρ d:ℝ}{E W U V:Credit}
variable {P:Era G ℝ}{R:Realm G (e+1) E}
local notation "Fz"=> PowerSeries.X
variable {F:Frames G}{A':Council F}{T':TowerP F}
lemma Respect.together {X':Era G ℝ}(f:Respect k e u 1 P B)(g:Respect k e u 1 X' B)(h:Respect k e u 1 (P-X') (B*Q))(v:0≤Q)(o:Cover): Fringed k e 0 0 B Q (shifted P o) (shifted X' o):=by
    have H:= f.care (o:=o) zero_le_one; have hh:= g.care (o:=o) zero_le_one; refine ⟨H.auth,hh.auth,v,fun i r u=>⟨H.anchor i u r,hh.anchor i u r,?_⟩⟩; exact (h.care (o:=o) zero_le_one).anchor i u r
namespace MergeTrip
local notation "Rι"=> (F.level h)
local notation "δ"=> sizeT R.draws ρ
variable (H:Hol G) (q:MergeTrip A' T' R.draws R.paid m b v c N h e k u Z)(x:Canopy R l c Z)(L:l≤b)
-- same clock N formal.
abbrev Tome (G:Gauge)(V:Credit)(k e u:ℕ)(K E W:Credit):= V.plus (cabin G k e u E W)
include q x L
local notation "U_" => shelterC H F A' h k u e
local notation "D_" => Credit.plus (U_) (cabin G k e u E W)
local notation "Φ"=> cruises R.draws R.paid N k v -- fn
lemma within (V:Dormitory R k u W)(f:Respect k e u 1 P B)(hp:b≤ i)(p:i≤v):
    Respect k e u 1 (cruises R.draws R.paid N k v i P) ((shelterC H F A' h k u e|>.plus (cabin G k e u E W)).buy Z*B) ∧
       Respect k e u 1 (cruises R.draws R.paid N k v i (q.openX H P)) ((shelterC H F A' h k u e|>.plus (cabin G k e u E W)).buy Z*B):=by
    let N' := x.cut (L.trans hp) p q.west; have hu:=q.reserve H; let FpV:=cabin G k e u E W; have hv:= voyage V N' (fun _=>1) (oldGuard N'.arch p) hu.cap f; change Respect _ _ _ 1 _ (((U_).plus FpV).buy Z*B) ∧ Respect _ _ _ 1 _ (((U_).plus FpV).buy Z*B); refine ⟨hv.rise (mul_le_mul_of_nonneg_right (Credit.thickened _ x.positive) f.nn),?_⟩
    have hh:= q.missing H f hp p; let X:=cruises R.draws R.paid N k v i P; let Y:=cruises R.draws R.paid N k v i (q.openX H P); rw [cruisePlus R.draws p R.hG R.green hu.cap f.auth (q.validated H _)] at hh; change Respect _ _ _ 1 Y _; rw [show Y=X-(X-Y) from by abel]; apply (hv.diff hh zero_le_one).rise; rw [add_comm]; let H':=(U_).buy Z; change H'*(_ * B) + _ ≤ _; have ht:paceT R.draws.S i v ^ h * B≤ B:= mul_le_of_le_one_left f.nn (pow_le_one₀ (pace_pos ..).le (pace_le _ p)); refine le_trans (add_le_add_left (mul_le_mul_of_nonneg_left ht (zero_le_one.trans (Credit.purchase U_ x.positive))) _) ?_; rw [← add_mul]; exact mul_le_mul_of_nonneg_right (Credit.fuel _ _ x.positive) f.nn
lemma straggler (g:Dormitory R k u W)(P:Fin (n+1)→ Era G ℝ)(a:Fin (n+1)→ℝ)(Y:Fin (n+1)→Cover)(f:∀ i,Respect k e u 1 (P i) (a i)):
     Respect ((n+1)*k) e 0 0 (embark (Φ b ∘ P) Y-embark (fun j=>Φ b (q.openX H (P j))) Y)
            (((coinMat ((n+1)*k) e)^n)*(∏ i,(D_).buy Z*a i)*(paceT R.draws.S b v)^h):=by
    let V:=D_; let K:=paceT R.draws.S b v^h; have hK:0≤ K:=pow_nonneg (pace_pos ..).le _; let B(i):=V.buy Z*a i; let X(i):=Φ b (P i); let Y'(i):=Φ b (q.openX H (P i)); let T(i):=shifted (X i) (Y i); let U(i):=shifted (Y' i) (Y i); have he(i): Fringed k e 0 0 (B i) K (T i) (U i):=by
       obtain ⟨h1,h2⟩:= within H q x L g (f i) (le_refl b) q.walk; have hb:= q.missing H (f i) (le_refl b) q.walk; rw [cruisePlus R.draws q.walk R.hG R.green (q.reserve H).cap (f i).auth (q.validated H _)] at hb; exact Respect.together h1 h2 (hb.rise (by rw [mul_comm (_^h),←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.thickens _ x.positive) (f i).nn) hK)) hK (Y i)
    have ht :(∑ _ : Fin (n+1),k)=(n+1)*k:= (by simp); have hv:= (Respect.stock (valueP n T U (fun _=>k) B ht.le he le_rfl)).2 -- after proof edit?
    rw [ht,loadRep] at hv; exact hv
local notation "κ'"=> ((n+1)*k)
-- lamp prices combined both real columns
omit q x L in
def husk (H:Hol G)(F:Frames G)(A':Council F)(k h e u n:ℕ)(E W U:Credit): Credit:= let F:= (shelterC H F A' h k u e).plus (cabin G k e u E W); (((cabin G ((n+1)*k) e 0 E U).prodC (pur (coinMat ((n+1)*k) e ^ n))).prodC (F.powC (n+1)))
lemma split_paint (g:Dormitory R k u W)(g':Dormitory R κ' 0 U)(d':SpringD R κ' 0 u V)(P:Fin (n+1)→Era G ℝ)(a:Fin (n+1)→ℝ) (w:ℕ→Fin (n+1)→Cover)(tρ:0<ρ)(td:0<d)(u':Cowrie R.draws b v w (SpanR R.draws ρ d))(f:∀ i, Respect k e u 1 (P i) (a i)):
    let F₁(P':Fin (n+1)→ Era G ℝ):=knotP (fun _=> P') w R N v l ((n+1)*k)
    let C:=LampTax G n k e u E V U (D_) d; let B:= ∏ i,a i; let U':=(sizeT R.draws ρ b)^u
    Respect ((n+1)*k) e 0 0 (F₁ P-F₁ (fun i=> q.openX H (P i))) (((C.plus C).buy Z*U'+(husk H F A' k h e u n E W U).buy Z*(paceT R.draws.S b v)^h)*B) := by -- Fι' typo
    intro F₁ C B U'; let X i j:= Φ i (P j); let P' j:=q.openX H (P j); let Y i j:= Φ i (P' j); let hu:=q.reserve H; let s p i:= knotP p w R N i l ((n+1)*k); have he:= q.walk; let L':=paceT R.draws.S b v^h; have hp:0≤ L':= pow_nonneg (pace_pos ..).le _
    have hx p(p':Fin (n+1)→ Era G ℝ)(ea:p=fun i j=> Φ i (p' j))(z:∀ i,b≤ i→i≤v→∀ j,Respect k e u 1 (p i j) ((D_).buy Z*a j)): Respect κ' e 0 0 (F₁ p'-s p b) (C.buy Z*(U'*B)):=by
        have hh: F₁ p'=s p v:= by unfold s F₁ knotP; simp_rw [ea,cruises_top]
        rw [hh]; have he:= summerPrice (x.cut (le_refl l) (L.trans he) q.west) u' tρ td g' d' L he hu.cap a (fun j=>0) (by simp) (fun i=>(f i).nn) D_ (fun i h u j=>by simpa only [ped, pow_zero,inv_one,mul_one] using z i h u j) (fun i h v j=>by rw [ea]; exact cruises_sub _ _ _ _ _ v) -- argument elaboration check
        simpa only [Finset.sum_const_zero,Nat.sub_zero] using he -- power_zero? δ^u
    let z':= D_; have hV(p:Credit):0≤p.buy Z:= zero_le_one.trans (p.purchase x.positive); have hb:0≤B:= Finset.prod_nonneg fun i _=>(f i).nn; have hb':0≤U':=pow_nonneg (sizeT_pos _ tρ _).le _
    have hΩ (i) (p:b≤ i)(h:i≤v)(j) : Respect k e u 1 (X i j) (z'.buy Z*a j) ∧ Respect k e u 1 (Y i j) (z'.buy Z*a j):= q.within H x L g (f j) p h; let H0:= hx X P rfl fun i a p j=>(hΩ i a p j).1; let H1:= hx Y P' rfl fun i a p j=>(hΩ i a p j).2
    have hT:= q.straggler H x L g P a (w b) f
    let K:=husk H F A' k h e u n E W U
    have hu1 : Respect κ' e 0 0 (s X b-s Y b) (K.buy Z*L'*B):=by
        let T:= x.cut (le_refl l) L (q.walk.trans q.west); have ht:= voyage g' T (fun _=>0) T.bare (q.walk.trans hu.cap) hT; change Respect _ _ _ _ (cruises R.draws R.paid N _ b l (MassP G ℝ n (fun j=>shifted (X b j) (w b j))- MassP G ℝ n (fun j=>shifted (Y b j) (w b j)))) _ at ht; rw [cruisePlus R.draws L R.hG R.green (q.walk.trans hu.cap) (MassP_auth _ (fun j=>(hΩ b le_rfl q.walk j).1.auth.shifted (w b j))) (MassP_auth _ (fun j=>(hΩ b le_rfl q.walk j).2.auth.shifted (w b j)))] at ht; apply ht.rise; unfold K husk; rw [Credit.products,Credit.products, Credit.power]; let C':= cabin G κ' e 0 E U; let D:= coinMat κ' e^n; have hw: (∏ j,z'.buy Z*a j)= (z'.buy Z)^(n+1)*B:=by rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin]
        change C'.buy Z*(D*(∏ j,z'.buy Z*a j)*L')≤ C'.buy Z* (pur D).buy Z*(z'.buy Z)^(n+1)*L'*B; rw [hw]; rw [show D*((z'.buy Z)^(n+1)*B)*L'= D*((z'.buy Z)^(n+1)*L'*B) by ring]; calc
             _≤ C'.buy Z*((pur D).buy Z*((z'.buy Z)^(n+1)*L'*B)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pure_goal ..) (mul_nonneg (mul_nonneg (pow_nonneg (hV z') _) hp) hb)) (hV _)
             _=_:=by ring
    rw [show F₁ P-F₁ P'= (F₁ P-s X b)-(F₁ P'-s Y b)+(s X b-s Y b) from by abel]; apply ((H0.diff H1 le_rfl).add hu1 le_rfl).rise; rw [add_mul]; apply add_le_add_left ?_; rw [← add_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.fuel _ _ x.positive) hb') hb
end MergeTrip
end YM.WilsonCoeffUV.Mer.Xa
