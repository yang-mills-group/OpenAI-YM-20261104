import YM.SignedWilsonExpansion.F9.Thawed
/-!
# Preserve Σ dimensions of charging joined full row when moving façade to inversion top

End price before rotation bound and finite-context project. In namespace `ShelfBook` for WCU quota, NOT the local two-step shelf. Keep (all) coefficients.
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
lemma FitS.stack (P:J→Cost)(S:Finset J)(C:J→ℝ)(f:∀ i∈S, FitS e (P i) (C i)): FitS e (∑ i∈ S,P i) (∑ i∈ S,C i):=by
   induction S using Finset.induction_on with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact FitS.zero
   | @insert i S h ih=> rw [Finset.sum_insert h,Finset.sum_insert h]; exact (f i (Finset.mem_insert_self ..)).plus (ih fun j hj=> f j (Finset.mem_insert_of_mem hj))
lemma FitS.mass (P:J→Cost)(S:Finset J)(C:J→ℝ)(f:∀ i∈S, FitS e (P i) (C i)): FitS e (∏ i∈S,P i) ((((e+1:ℕ):ℝ)^S.card)*(∏ i∈ S,C i)):=by
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.prod_empty, Finset.card_empty,pow_zero,mul_one]; exact (by simpa only [map_one,abs_one] using FitS.C (e:=e) 1)
   | @insert i S h ih=> rw [Finset.prod_insert h,Finset.prod_insert h,Finset.card_insert_of_notMem h]; exact ((f i (Finset.mem_insert_self ..)).product (ih (fun j hj=>f j (Finset.mem_insert_of_mem hj)))).more (le_of_eq (by ring))
-- pointer power.Col.L. mark
namespace MergeTrip
local notation "Rι"=> (F.level h)
local notation "κ'"=> ((n+1)*k)
local notation "δ" => sizeT R.draws ρ
variable (H:Hol G) (q:MergeTrip A' T' R.draws R.paid m b v c N h e k u Z) (x:Canopy R l c Z)(L:l≤v)
def cFees (ρ:ℝ)(l:ℕ) (P:Era G ℝ) (i:(F.level h).Index): Cost:= toward R.draws R.paid N l v (q.pen H P ρ i)
-- `relativeF` units, scope to `Ω`; not altered. Book field linear (later)
include q x L
omit q x L in
def writePrice (H:Hol G)(F:Frames G)(A':Council F)(k h e u:ℕ)(E:Credit):= (Canopy.pageS G (e+1) E).prodC (shelterC H F A' h k u e) -- type?
lemma feesSphere (hρ:0<ρ)(i:(F.level h).Index)(f:Respect k e u 1 P B):
     FitS e (q.cFees H ρ l P i) ((writePrice H F A' k h e u E).buy Z*(B*(δ v)^wt (F.level h) i)):=by
    unfold writePrice; rw [Credit.products,mul_assoc]; exact ((x.cut (le_refl l) L q.west).direction_cost (q.reserve H).cap (q.pen_paid H f i hρ) (by omega)).1
-- billing timestamp; reading t=date v already a pivot in metadata. Note conceptual A corresponds to `K`.
omit q x L in
abbrev sendPrice (k h e u n:ℕ)(E:Credit)(H:Hol G)(F:Frames G)(A':Council F): Credit:= ((writePrice H F A' k h e u E).powC (n+1)).prodC (pur (((e+1:ℕ):ℝ)^(n+1)))
lemma cost_many (a:Fin (n+1)→ℝ)(P:Fin (n+1)→Era G ℝ)(w:∀ i,Respect k e u 1 (P i) (a i))(β:Fin (n+1)→(F.level h).Index)(hρ:0<ρ): FitS e (∏ i,q.cFees H ρ l (P i) (β i)) ((sendPrice k h e u n E H F A').buy Z*((∏ i,a i)*(δ v)^(∑ i,wt (F.level h) (β i)))):=by
    let C:=writePrice H F A' k h e u E; let χ:=C.buy Z; let X i:= wt _ (β i); have ht:= FitS.mass _ Finset.univ _ (fun i _=> q.feesSphere H x L hρ (β i) (w i)); apply ht.more; unfold sendPrice; rw [Credit.products, Credit.power, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; let T:=χ^(n+1); let A:=∏ i,a i; let D:=δ v; have hT:0≤T:= pow_nonneg (zero_le_one.trans (C.purchase x.positive)) _; let L:= D^(∑ i,X i); have hz:0≤L:= pow_nonneg (sizeT_pos _ hρ _).le _; let V:=((e+1:ℕ):ℝ)^(n+1); have ha:0≤A:= Finset.prod_nonneg fun i _=> (w i).nn; change V*(T*(A*L))≤ T*(pur V).buy Z*(A*L); rw [←mul_assoc,mul_comm V]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pure_goal ..) hT) (mul_nonneg ha hz)
-- bill isolated mark path gap.Cover retains position shape v or c. Both priced with arm launch.m.
omit q x L in
def sendTax (k h e u n:ℕ)(E W U:Credit)(H:Hol G)(F:Frames G)(A':Council F)(d:ℝ): Credit:= let X:=sendPrice k h e u n E H F A'; let Y:= LampTax G n k e u E W U (Stair.lightFee H F A' h k u e) d; (((pur ((e+1:ℕ):ℝ)).prodC X).prodC Y)
include q
omit x L in
def launched (P:Fin (n+1)→Era G ℝ)(w:ℕ→Fin (n+1)→Cover)(l:ℕ)(ρ:ℝ)(d:ℕ): Cost:= ∑ f: Fin (n+1)→(F.level h).Index,(∏ i,q.cFees H ρ l (P i) (f i)) * (dew (knotP (fun i j=> q.cohort.tab ρ i (f j)) w R N d l κ'))
lemma reachBook (hρ:0<ρ)(P:Fin (n+1)→Era G ℝ)(w:ℕ→Fin (n+1)→Cover):
    FadeRaw R.draws R.paid N κ' l v (embark (fun i=> q.openX H (P i)) (w v))= q.launched H P w l ρ v:=by
    unfold launched
    simp_rw [q.opening H _ hρ]; exact seasonH (fun i j=> q.cohort.tab ρ v j) (w v) (fun i=>q.pen H (P i) ρ) R.hG R.green L (q.reserve H).cap (fun i j=>(q.cohort.tab_meter H hρ (q.berth.trans q.walk) q.west j).auth)
omit q x L in
def remit (k h e u n:ℕ)(E W U:Credit)(H:Hol G)(F:Frames G)(A':Council F)(d:ℝ): Credit:= let C:= sendTax k h e u n E W U H F A' d; C.prodC (pur ((Fintype.card (Fin (n+1)→(F.level h).Index)):ℝ))
-- sibling split with gains
lemma reachGap (W':SpringD R κ' 0 u W)(U':Dormitory R κ' 0 U)(hρ:0<ρ)(V:(n+1)*h≤ u) (P:Fin (n+1)→Era G ℝ)(a:Fin (n+1)→ℝ)(f:∀ i,Respect k e u 1 (P i) (a i))(d:ℝ)(p:0<d) (w:ℕ→Fin (n+1)→Cover)(t:Cowrie R.draws v c w (SpanR R.draws ρ d)): FitS e (q.launched H P w l ρ c-q.launched H P w l ρ v) ((remit k h e u n E W U H F A' d).buy Z*((δ v)^u*(∏ i,a i))):=by
    let S(f:Fin (n+1)→(F.level h).Index)(b):= dew (knotP (fun i j=>q.cohort.tab ρ i (f j)) w R N b l κ'); let T:= sendTax k h e u n E W U H F A' d; let A:=∏ i,a i; let D:=δ v; have ha:0≤A:= Finset.prod_nonneg fun i _=> (f i).nn; have he:0<D:=sizeT_pos _ hρ _; let XF(f:Fin (n+1)→(F.level h).Index):Cost:=∏ i,q.cFees H ρ l (P i) (f i)
    let L₀:= A*(δ v)^u; have hb:0≤ L₀:=mul_nonneg ha (pow_nonneg he.le _); let U₁:=(T.buy Z*L₀)
    have hx x' : FitS e (XF x'* S x' c-XF x'* S x' v) U₁:=by
       let W':= W'; let K':=∑ i, wt _ (x' i); have hw: K' ≤ u:= le_trans (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _:Fin (n+1)=>h) fun i _=>(F.level h).bound (x' i)) (by simpa)
       rw [←mul_sub]; have hY:=q.cost_many H x L a P f x' hρ; have ht:= Lamp_seen H q.cohort x t hρ p U' W' x' (q.berth.trans q.walk) q.west L hw; have hv:= dew_auth ht (le_refl 0); rw [dew_sub] at hv
       apply (hY.product hv).more
       conv_rhs => (unfold U₁ T; simp only [sendTax]; rw [Credit.products,Credit.products])
       let B:ℝ:=(e+1:ℕ); let X:=(sendPrice k h e u n E H F A').buy Z; let Y:=(LampTax G n k e u E W U (Stair.lightFee H F A' h k u e) d).buy Z; let D':=(D^K')
       have hh:D^K' * D^(u-K')=D^u:=(by rw [←pow_add, Nat.add_sub_of_le hw]); have hx:1≤Z:=x.positive; have hX:0≤X:=zero_le_one.trans (Credit.purchase _ hx); have hY:0≤Y:= zero_le_one.trans (Credit.purchase _ hx)
       change B*(X*(A*D^K')*(Y*D^(u-K')))≤(pur B).buy Z*X*Y*L₀
       rw [show B*(X*(A*D^K')*(Y*D^(u-K')))=B*X*Y*L₀ by unfold L₀; change _=B*X*Y*(A*D^u); rw [← hh]; ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal ..) hX) hY) hb
    unfold launched; rw [← Finset.sum_sub_distrib]; apply (FitS.stack _ Finset.univ _ (fun i _=> hx i)).more; unfold remit; rw [Credit.products,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; let K:ℝ:=(Fintype.card (Fin (n+1)→(F.level h).Index)); change K*(T.buy Z*L₀)≤T.buy Z*(pur K).buy Z*(D^u*A); rw [←mul_assoc,mul_comm K,mul_comm (D^u)]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pure_goal ..) (zero_le_one.trans (T.purchase x.positive))) hb
end MergeTrip
end YM.WilsonCoeffUV.Mer.Xa
