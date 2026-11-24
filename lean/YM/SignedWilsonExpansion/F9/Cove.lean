import YM.SignedWilsonExpansion.F9.ShelfPrice
/-!
# All weights, all separations. Terminal connection bill.
-/
set_option autoImplicit false
set_option maxHeartbeats 740000
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
namespace MergeTrip
local notation "Rι"=> (F.level h)
local notation "κ'"=> ((n+1)*k)
local notation "δ" => sizeT R.draws ρ
variable (H:Hol G)(q:MergeTrip A' T' R.draws R.paid m b v c c h e k u Z)(x:Canopy R l c Z)(L:l≤b)
def draftA (H:Hol G)(F:Frames G)(A':Council F)(k h e u n:ℕ)(d:ℝ)(E U W V:Credit): Credit:= let S:= LampTax G n k e u E V U ((shelterC H F A' h k u e).plus (cabin G k e u E W)) d
                                        ((S.plus S).plus (remit k h e u n E V U H F A' d)).plus (husk H F A' k h e u n E W U)
include x L in
lemma write_cost (W':Dormitory R k u W)(U':Dormitory R κ' 0 U)(V':SpringD R κ' 0 u V)(hρ:0<ρ)(hp:(n+1)*h≤u)
    (P:Fin (n+1)→Era G ℝ)(a:Fin (n+1)→ℝ)(f:∀ i,Respect k e u 1 (P i) (a i))(p:0<d)(w:ℕ→Fin (n+1)→ Cover)(t:Cowrie R.draws b c w (SpanR R.draws ρ d)):
    FitS e (q.launched H P w l ρ c-FadeRaw R.draws R.paid c κ' l v (embark P (w v))) ((draftA H F A' k h e u n d E U W V).buy Z*((δ b)^u+ (paceT R.draws.S b v)^h)*(∏ i,a i)):=by
    let C:=q.launched H P w l ρ v; let Q:= q.openX H; let F':= FadeRaw R.draws R.paid c κ' l v; let X:=F' (embark P (w v)); let D:=q.launched H P w l ρ c; have hv := split_paint H q x L W' U' V' P a w hρ p (t.cuts (le_refl b) q.west) f; have hy:F' (embark (fun i=> Q (P i)) (w v))=C:= reachBook H q x (L.trans q.walk) hρ P w
    let V₁:= remit k h e u n E V U H F A' d; let V₂:= husk H F A' k h e u n E W U; let X':= LampTax G n k e u E V U ((shelterC H F A' h k u e).plus (cabin G k e u E W)) d; let V₀:=X'.plus X'; let β:=paceT R.draws.S b v^h; let α:= (δ b)^u; let α':=(δ v)^u; let B:= ∏ i,a i
    have hu:=dew_auth hv le_rfl; have hh:FitS e (X-C) ((V₀.buy Z *α+V₂.buy Z*β)*B):=by rw [dew_sub] at hu; rw [←hy]; exact hu
    have he:= q.reachGap H x (L.trans q.walk) V' U' hρ hp P a f d p w (t.cuts q.walk le_rfl); change FitS e (D-X) _; rw [show D-X=(D-C)-(X-C) by abel]; apply (he.minus hh).more
    let K:=(V₀.plus V₁).plus V₂; have h0:=x.positive; have hf(C:Credit):0≤ C.buy Z:=zero_le_one.trans (C.purchase h0); have ht:α'≤ α:=pow_le_pow_left₀ (sizeT_pos _ hρ v).le (anti_sizeT R.draws hρ q.walk) _; have hβ:0≤β:=pow_nonneg (pace_pos ..).le _; have ha:0≤α:=pow_nonneg (sizeT_pos _ hρ b).le _; have hb:0≤ B:= Finset.prod_nonneg fun i _=> (f i).nn
    change V₁.buy Z*(α'*B)+(V₀.buy Z*α+V₂.buy Z*β)*B≤ K.buy Z*(α+β)*B; rw [←mul_assoc,←add_mul]; refine mul_le_mul_of_nonneg_right (le_trans (add_le_add_left (mul_le_mul_of_nonneg_left ht (hf _)) _) (?_)) hb; rw [←add_assoc,← add_mul, add_comm (V₁.buy Z),mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right ((Credit.fuel _ _ h0).trans (Credit.thickens _ h0)) ha) (mul_le_mul_of_nonneg_right (Credit.thickened _ h0) hβ)

-- m=f? b reporter f. stop r precedes, m coarse-grid, v=K, c inversion top n'. l=ℓ. N actual larger.
def sprayC (G:Gauge)(k e n:ℕ)(E U:Credit): Credit:= ((vaporC G ((n+1)*k) e E U).plus (windy G ((n+1)*k) e 0 E U)).prodC (pur ((coinMat ((n+1)*k) e)^n))
-- r stop corresponding to F9, not the index on m smoothing teacher
lemma hit (x' : Canopy R l v Z)(u':Dormitory R κ' 0 U)(p:l≤ r)(w:r≤ v)(t:v≤ c)(v':c≤N)
    (P:Fin (n+1)→ Era G ℝ)(a:Fin (n+1)→ℝ)(f:∀ i,Respect k e u 1 (P i) (a i))(s:Fin (n+1)→ Cover):
    FitS e (rear R.draws R.paid c l r (FadeRaw R.draws R.paid c κ' l v (embark P s))-FadeRaw R.draws R.paid N κ' r v (embark P s)) ((sprayC G k e n E U).buy Z*(R.tempC r v+R.tempC v c)* (∏ i,a i)):=by
    let B:= ∏ i,a i; let E':=coinMat κ' e^n; let Q:=embark P s; have he :(∑ _ : Fin (n+1),k)=(n+1)*k:=by simp
    have hp:= embarkMoney P s a (fun _=>k) f he.le; rw [he] at hp; apply (warmth_fee u' x' hp p w t v' le_rfl).more
    unfold sprayC; rw [Credit.products]; let J:= R.tempC r v; let X:= R.tempC v c; let A:= vaporC G κ' e E U; let D:= windy G κ' e 0 E U; have hb0:0≤B:= Finset.prod_nonneg fun i _=> (f i).nn; have hE:0≤E':= pow_nonneg (coinMat_nn ..) _; have hv:1≤Z:=x'.positive
    have hj:0≤J:= (trail_pos ..).le; have hx:0≤X:= (trail_pos ..).le; let C:= (A.plus D).buy Z; have hc:0≤ C:=zero_le_one.trans (Credit.purchase _ hv)
    change A.buy Z*J*(E'*B)+ D.buy Z*(E'*B)*X≤ C*(pur E').buy Z*(J+X)*B
    rw [mul_right_comm _ _ X, ←add_mul]; refine (mul_le_mul (add_le_add (mul_le_mul_of_nonneg_right (Credit.thickens D hv) hj) (mul_le_mul_of_nonneg_right (Credit.thickened A hv) hx)) (mul_le_mul_of_nonneg_right (pure_goal E' Z) hb0) (mul_nonneg hE hb0) (add_nonneg (mul_nonneg hc hj) (mul_nonneg hc hx))).trans_eq ?_; change (C*J+C*X)*_= _; ring

def finish (H:Hol G)(F:Frames G)(A':Council F)(k h e u n:ℕ)(d:ℝ)(E U W V:Credit): Credit:= ((Canopy.pageS G (e+1) E).prodC (draftA H F A' k h e u n d E U W V)).plus (sprayC G k e n E U)
include q x L
/-- This is before θ or ζ evaluation; normalized comparison at same clock, with poles paid in native K cost of actual P. `F9` uses P out of the actual page. Query step retains this semantics. -/
theorem cover_price (g:Dormitory R κ' 0 U)(W':Dormitory R k u W)(V':SpringD R κ' 0 u V) (t:l≤ r)(y:r≤ v)(n':c≤ N) (hρ:0<ρ)(hd:0<d)(θ:(n+1)*h≤u)
    (P:Fin (n+1)→Era G ℝ)(a:Fin (n+1)→ℝ)(s:ℕ→Fin (n+1)→Cover) (w:Cowrie R.draws b c s (SpanR R.draws ρ d)) (f:∀ i,Respect k e u 1 (P i) (a i)): let X:=(embark P (s v))
    FitS e (rear R.draws R.paid c l r (q.launched H P s l ρ c) - FadeRaw R.draws R.paid N κ' r v X) ((finish H F A' k h e u n d E U W V).buy Z*((δ b)^u+(paceT R.draws.S b v)^h+(R.tempC r v+R.tempC v c))*(∏ i,a i)):=by
    intro X; let Y:=rear R.draws R.paid c l r; let F':=FadeRaw R.draws R.paid c κ' l v X; let C':= FadeRaw R.draws R.paid N κ' r v X; let Q:= q.launched H P s l ρ c
    have hx:=L.trans q.walk; have ht:=(x.cut (le_refl l) hx q.west); have h0:=x.positive; let Vv:= hit (N:=N) (c:=c) ht g t y q.west n' P a f (s v); have he:= q.write_cost H x L W' g V' hρ θ P a f hd s w; have hh :=((x.cut (le_refl l) t (y.trans q.west)).direction_cost (y.trans q.west) he (by omega)).2; change FitS _ (Y Q-C') _; rw [show Y Q-C'=Y (Q-F')+(Y F'-C') by rw [map_sub]; abel]; apply (hh.plus Vv).more
    let P':=draftA H F A' k h e u n d E U W V; let D:= (Canopy.pageS G (e+1) E).prodC P'; let Q:=sprayC G k e n E U; let V':= D.plus Q; let α:=(δ b)^u+(paceT R.draws.S b v)^h; let β:= R.tempC r v+R.tempC v c; let B:=∏ i,a i; have ha:0≤α:=add_nonneg (pow_nonneg (sizeT_pos _ hρ b).le _) (pow_nonneg (pace_pos ..).le _); have hb:0≤B:= Finset.prod_nonneg fun i _=>(f i).nn; have hβ:0≤β:=add_nonneg (trail_pos ..).le (trail_pos ..).le
    change (Canopy.pageS _ _ E).buy Z*(P'.buy Z*α*B)+ Q.buy Z*β*B ≤ V'.buy Z*(α+β)*B; rw [←mul_assoc,←mul_assoc,←Credit.products,←add_mul,mul_add (V'.buy Z) α β]; exact mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right (Credit.thickens Q h0) ha) (mul_le_mul_of_nonneg_right (Credit.thickened D h0) hβ)) hb
end MergeTrip
end YM.WilsonCoeffUV.Mer.Xa
