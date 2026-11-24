import YM.SignedWilsonExpansion.F9.Sandal
/-!
# Separated course.Purchase pressure Join for full finite Σ. Anchor-root charge can move with placements; require every face at the same node set position, high moment gain pays E. Combine `windy` later.
-/
set_option autoImplicit false
set_option maxHeartbeats 780000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open Wheel.Mark (pieceO piece_auth)
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e s k h m c v b T N M i j l r p u n :ℕ}
variable {B Q D Z X Y η t a:ℝ}{E W U:Credit}
variable {P:Era G ℝ}{R: Realm G (e+1) E}
local notation "terr"=> Bank.terrain
local notation "adm" => R.draws
abbrev under (S:Schedule)(m:ℕ)(x:Cover): Cover:=(S.block m).val • x
abbrev childFrom (A:Levels G)(m:ℕ):= under A.S m
lemma parent_from (x:Cover) : parentC (A.S.block m) (childFrom A m x)=x:=by
    let L:= A.S.block m; have hp : parentC L (L.val • x+lift (0:Site L))=x:= congr_arg Prod.fst ((panel L Unit).symm_apply_apply (x,(0:Site L),())); simpa only [coat0, add_zero] using hp
private abbrev panelP (x:Cover):ProfileW:= fun i=>Bank.terrain.gap x i
variable (u': Fin (n+1)→Cover)(B':Fin (n+1)→ℝ)
lemma spreadX (p q:Cover)(v: t≤ (Bank.terrain.gap p q:ℝ))(h:0<t): SplitHill (panelP p) (panelP q) 0 1 t:=by
    refine ⟨fun i j=>Bank.terrain.tri _ _ _,fun i j=>Bank.terrain.tri _ _ _,le_rfl,h,le_rfl,zero_le_one,fun i=> by simp only [zero_mul]; positivity,fun i=>by simp only [zero_mul]; positivity, fun i j => v.trans (?_)⟩
    have hp : (Bank.terrain.gap p q :ℝ) ≤ (Bank.terrain.gap p i:ℝ)+Bank.terrain.gap i j+Bank.terrain.gap q j:=by exact_mod_cast (le_trans (Bank.terrain.tri p i q) (le_trans (Nat.add_le_add_left (Bank.terrain.tri i j q) _) (le_of_eq (by rw [Bank.terrain.swap j q];exact (Nat.add_assoc ..).symm)))) -- add_le see
    unfold panelP; linarith only [hp]
lemma ladderCost (A:Levels G)(m:ℕ)(x:Cover)(y:dock Cover (Hooks G) r)(u:ℕ): let p:= childFrom A m x; quoteT (heirP A m (panelP x)) u y ≤ 9^u * hedge p 1 u y:=by
    intro p; let W:=heirP A m (panelP x); let Q:= tread terr p y; let L:=A.S.block m
    have hg: Ridge W y≤ Q+8:=by
        apply Ridge.cap; intro j; let v:=(y j).1; change Bank.terrain.gap x (parentC L v) ≤ _
        have hx : L.val*Bank.terrain.gap x (parentC L v) ≤ Q+8*L.val:=by nth_rw 1 [← show parentC L p= x from parent_from x]; exact le_trans (parent_stride p v) (Nat.add_le_add_right (leg_le terr (stud p y) 0 j.succ) _)
        refine Nat.le_of_mul_le_mul_left (le_trans hx (le_trans (Nat.add_le_add_right (le_mul_of_one_le_left (Nat.zero_le Q) L.pos) _) (le_of_eq (show L.val*Q+8*L.val=L.val*(Q+8) from by ring)))) L.pos
    apply (autumn_mono zero_le_one u hg).trans; apply (autumn_tax zero_le_one _ _ u).trans; simp only [show autumn 1 u 8=9^u by norm_num [autumn]]; exact le_of_eq (mul_comm ..) -- autumn args
lemma Respect.shiftedMoney (f:Respect k e u 1 P B)(d:Cover)(hl:l≤e): Fruit d 1 u ((shifted P d).2 l r) B:=by
    exact (show Fruit d 1 u (revolve d (P.2 _ _)) B from by simpa only [add_zero] using (f.anchor l (by assumption) r).turn d)
lemma Respect.join_supplied (f:Respect k e u 1 P B)(A:Levels G)(d:Cover)(v:0≤η): let p:=childFrom A m d; PaidMer e u (heirP A m (panelP d)) (shifted P p) (shifted P p) (9^u*B) η:=by
    intro p i j w; let L:=heirP A m (panelP d); let F:= (shifted P p); let X:=(shifted P p).2 i j
    have hx:= ladderCost A m d (r:=j); have he d (t:0≤d):0≤ d*B:=mul_nonneg t f.nn; have G':0≤(9:ℝ)^u:=by positivity
    have hp: Rent L u X (9^u*B):= budget_minor (cap_scale (f.shiftedMoney (r:=j) p w) G') (fun i=> mul_nonneg (zero_le_one.trans (quoteT_pos i ..)) (norm_nonneg _)) (fun i=>(mul_le_mul_of_nonneg_right (hx i u) (norm_nonneg _)).trans_eq (by rw [mul_assoc])) -- might need explicit
    exact ⟨hp,hp,by rw [sub_self]; exact Award.zero.more (mul_nonneg hp.C v)⟩
abbrev embark (P:Fin (n+1)→Era G ℝ)(u: Fin (n+1)→Cover): Era G ℝ:= MassP G ℝ n fun i=> shifted (P i) (u i)
-- All launch cashes for limiting regulator N only. Clock ν.Top on ambient.
def sponsorX (G:Gauge)(n k e u:ℕ)(E W:Credit):= (priceWG G e k 0 u E W).prodC (pur ((n:ℝ)*(coinMat k e+1)^n*((9:ℝ)^u)^(n+1)))
lemma embarkMoney (P:Fin (n+1)→Era G ℝ)(u':Fin (n+1)→Cover)(B':Fin (n+1)→ℝ)(h:Fin (n+1)→ℕ)(f:∀ i,Respect (h i) e u 1 (P i) (B' i)) (v:(∑ i,h i) ≤ k):Respect (∑ i,h i) e 0 0 (embark P u') ((coinMat k e)^n * ∏ i,B' i):= by
    exact Respect.fixtures _ _ h le_rfl v fun i=>(f i).care zero_le_one
lemma gapCharge (P:Fin (n+1)→ Era G ℝ)(q:SpringD R k 0 u W)(h:Fin (n+1)→ℕ)(u': Fin (n+1)→Cover)(v:t>0)(w:∀ i j,i≠j → t≤ (Bank.terrain.gap (u' i) (u' j):ℝ)) (f:(∑ i,h i)≤k)(p:R.anchor≤m)(x:m<N)
    (B': Fin (n+1)→ℝ)(T₁:∀ i,Respect (h i) e u 1 (P i) (B' i))(T₂:∀ i,Respect (h i) e u 1 (verseI adm R.paid m N (h i) (P i)) (B' i)):
    let Q:= verseI adm R.paid m N (∑ i,h i) (embark P (fun i=>childFrom adm m (u' i)))-embark (fun i=>verseI adm R.paid m N (h i) (P i)) u'; Respect (∑ i,h i) e 0 0 Q (R.cash (sponsorX G n k e u E W) m*((t^u)⁻¹ * ∏ i,B' i)):=by
    intro S; let d:=δWarm R m N; let P'(i):=shifted (P i) (childFrom adm m (u' i)); let A'(i): Era G ℝ → Era G ℝ := verseI adm R.paid m N (h i); let X'(i):=(9:ℝ)^u*B' i
    have h0:0≤d:= (ReelTime R (le_refl e) p x (le_refl N) (le_refl N)).θ
    have he(i):A' i (P' i)=shifted (A' i (P i)) (u' i):= outing adm x R.hG R.green (T₁ i).auth _
    have hz:S=DeltaGap adm R.paid m N P' h:= by unfold DeltaGap startK; simp_rw [show ∀ i, verseI adm R.paid m N (h i) (P' i)= _ from he]; rfl
    have HT(i): 0≤B' i:= (T₂ i).nn
    have hA:= drifted n P' P' h X' (panelP ∘ u') le_rfl v f le_rfl (fun i j u=>spreadX _ _ (w i j u) v) q p x le_rfl le_rfl le_rfl (fun i=>(T₁ i).auth.shifted _) (fun i=>(T₁ i).auth.shifted _) (fun i=> by rw [Nat.zero_add]; exact (T₁ i).join_supplied adm _ h0) (fun i=>(by change Fringed (h i) _ _ _ _ _ (A' i _) (A' i _); rw [he i]; exact ((T₂ i).care zero_le_one).paired h0 |>.pay (le_mul_of_one_le_left (HT i) (one_le_pow₀ (by norm_num : (1:ℝ)≤9)))))
    rw [hz]; apply ((Respect.stock hA).1).rise; unfold cash sponsorX; rw [loadRep,pearlB,Credit.products,pow_zero,mul_one]; let C:= priceWG G e k 0 u E W; let L:ℝ:= n; let F:= C.buy (R.y m); have hc:0≤ F:= zero_le_one.trans (C.purchase (R.depth _ p)); let S:= ∏ i,B' i; have hs:0≤S:= Finset.prod_nonneg fun i _=>HT i; let V:= L*(coinMat k e+1)^n*((9:ℝ)^u)^(n+1)
    have Hb:0≤ (t^u)⁻¹:=by positivity
    refine le_trans (le_of_eq (show n*F*(t^u)⁻¹ *(_ * ∏ i,X' i)= F*V*((t^u)⁻¹*S) from ?_)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pure_goal V _) hc) (mul_nonneg Hb hs))
    unfold X' S V L; rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ, Fintype.card_fin]; ring
end YM.WilsonCoeffUV.Mer.Xa
