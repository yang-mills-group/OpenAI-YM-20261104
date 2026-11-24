import YM.SignedWilsonExpansion.F9.Pedals
/-!
# Cruise and tab estimations with dimension factors exposed

Flat reporter weight prices may be large as μ^k/h_*^Σ.
Products recover left normalization by point matching. Stop book.
`careStart` gives the a0 crop -- integrated comparison later. Expose E clock costs
independently of regulator→MS.Poly product coupons. Keep ∏ real amplitudes.
-/
set_option autoImplicit false
set_option maxHeartbeats 760000
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
local notation "Σk" => (n+1)*k
variable {P:ℕ→ Fin (n+1)→Era G ℝ}{x:ℕ→ Fin (n+1)→Cover}{R:Realm G (e+1) E}
protected def summerP (G:Gauge) (n k e u:ℕ)(E W U:Credit) := ((Jetty.yieldT G n ((n+1)*k) ((n+1)*k) e u E W U).prodC Credit.leanC).prodC Credit.unit
abbrev LampTax (G:Gauge) (n k e u:ℕ)(E W U V:Credit) (d:ℝ) := let L:=Xa.summerP G n k e u E W U; L.prodC (((E.powC u).prodC (V.powC (n+1))).prodC (pur ((d^u)⁻¹)))
lemma summerPrice (q:Canopy R m c Z)(g:Cowrie R.draws v c x (SpanR R.draws ρ d))(vρ:0<ρ)(vd:0<d)
    (T':Dormitory R ((n+1)*k) 0 U)(W':SpringD R ((n+1)*k) 0 u W)(b':m≤v)(k':v≤c)(v':c≤N)
    (a:Fin (n+1)→ℝ)(D:Fin (n+1)→ℕ)(p:(∑ i,D i) ≤u) (f:∀ i,0≤a i)(V:Credit)(w:∀ i,v≤ i→i≤ c →∀ j,Respect k e u 1 (P i j) (ped R.draws ρ a D (V.buy Z) i j))(t:∀ i,v≤ i→ i<c→∀ j, P i j=verseI R.draws R.paid i N k (P (i+1) j)):
    Respect ((n+1)*k) e 0 0 (knotP P x R N c m ((n+1)*k)-knotP P x R N v m ((n+1)*k)) ((LampTax G n k e u E W U V d).buy Z * ((sizeT R.draws ρ v)^(u-∑ i,D i) * ∏ i,a i)):=by
    let Q:=Jetty.engine V (q.cut b' k' le_rfl) vρ vd g a D P p f t w
    let B:= sizeT R.draws ρ v; have hb:= sizeT_pos R.draws vρ v; let F:= taxesR d Z B a D u E V; have hf:0≤F:=taxes_nn vd q.positive hb.le f D u E V
    have he :(∑ _ : Fin (n+1),k)=(n+1)*k:=by simp
    have hv:= Q.carry (U:=U) (he ▸ T') W' q b' v' he.le hf k'; rw [he] at hv; apply hv.rise
    unfold LampTax Xa.summerP; simp only [Credit.products, Credit.unit_cost,mul_one]; let J := (Jetty.yieldT G n ((n+1)*k) ((n+1)*k) e u E W U).buy Z*Credit.leanC.buy Z
    let T:=∑ i,D i; let A':=∏ i,a i; let Y:=(E.powC T).buy Z*(V.powC (n+1)).buy Z; let X:= (E.powC u).buy Z*(V.powC (n+1)).buy Z; let K:= (d^u)⁻¹; let L:= (pur K).buy Z; have ho:= q.positive
    have hp1(C:Credit):0≤ C.buy Z:=zero_le_one.trans (C.purchase ho)
    have hu: Y≤ X:= by unfold Y X; rw [Credit.power E Z T,Credit.power E Z u]; apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (E.purchase ho) p) (hp1 _)
    have hy:0≤Y:=mul_nonneg (hp1 _) (hp1 _); have hL:0≤ K:=inv_nonneg.mpr (pow_nonneg vd.le _); have ha:0≤A':= Finset.prod_nonneg fun i _=> f i; let b:=B^(u-T); have hx:0≤b:= pow_nonneg hb.le _; have hJ:0≤ J:= mul_nonneg (hp1 _) (hp1 _)
    change J*(A'*K*b*Y)≤ J*(X*L)*(b*A'); rw [mul_assoc J (X*L)]; refine mul_le_mul_of_nonneg_left ?_ hJ; rw [show A'*K*b*Y= Y*K*(b*A') by ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul hu (pure_goal ..) hL (hy.trans hu)) (mul_nonneg hx ha)
-- unit `.pad` reader
lemma Lamp_seen (H:Hol G) {L:Frames G}{A':Council L}{Q:TowerP L} (p':Stair A' Q R.draws R.paid m c N h e k u Z)(q:Canopy R b c Z)(g:Cowrie R.draws v c x (SpanR R.draws ρ d))(vρ:0<ρ)(vd:0<d) (D':Dormitory R ((n+1)*k) 0 U)(W':SpringD R ((n+1)*k) 0 u W)(y:Fin (n+1)→(L.level h).Index)(m':m≤v)(v':v≤c)(b':b≤v)(p:(∑ i,wt _ (y i)) ≤u):
     let X:=fun i (j:Fin (n+1))=> p'.tab ρ i (y j); let w j:= wt (L.level h) (y j); Respect ((n+1)*k) e 0 0 (knotP X x R N c b ((n+1)*k)-knotP X x R N v b ((n+1)*k)) ((LampTax G n k e u E W U (Stair.lightFee H L A' h k u e) d).buy Z*(sizeT R.draws ρ v)^(u-∑ i,w i)):=by
    intro X w; have hb0:= p'.charm h le_rfl;
    have he i (e':v≤ i)(u':i≤c)(j:Fin (n+1)): Respect k e u 1 (p'.tab ρ i (y j)) (ped R.draws ρ (fun _=>1) w ((Stair.lightFee H L A' h k u e).buy Z) i j):=by unfold ped; rw [one_mul]; exact p'.tab_meter H vρ (m'.trans e') u' _
    refine (summerPrice q g vρ vd D' W' b' v' hb0.cap (fun _=>1) w p (fun _=>zero_le_one) _ he (fun i h v j=> p'.transmit H vρ (m'.trans h) v (y j)
    )).rise ?_; rw [Finset.prod_const_one,mul_one]
/-- At any v witness poly bound after paying leading dimensions. Later we'll use `Dev` at a0 w/ inverse spacing poly to resolve regulated row budget on reflected points.Delta requires here `δ≤1`. -/
lemma Lamp_rung (H: Hol G){L:Frames G}{A':Council L}{Q:TowerP L} (p':Stair A' Q R.draws R.paid m c N h e k u Z)(vρ:0<ρ) (m':m≤v)(v':v≤c)(cap:(sizeT R.draws ρ v)≤1) (y:Fin (n+1)→(L.level h).Index) (x':Fin (n+1)→Cover):
    Respect ((n+1)*k) e 0 0 (embark (fun j=>p'.tab ρ v (y j)) x') (((((Stair.lightFee H L A' h k u e).powC (n+1)).prodC (pur ((coinMat ((n+1)*k) e)^n))).buy Z)*(((sizeT R.draws ρ v)^((n+1)*h))⁻¹)):=by
    let T:= Stair.lightFee H L A' h k u e; let V:= sizeT R.draws ρ v; have hv:= sizeT_pos R.draws vρ v; have hp:1≤ Z:= (p'.charm h le_rfl).pos; have h0:0≤T.buy Z:=zero_le_one.trans (T.purchase hp)
    let K:= T.buy Z*(V^h)⁻¹; have hg i: Respect k e u 1 (p'.tab ρ v (y i)) K:= by
       have hl:(V^h) ≤ V^(wt _ (y i)):= pow_le_pow_of_le_one hv.le cap ((L.level h).bound _); exact (p'.tab_meter H vρ m' v' (y i)).rise (mul_le_mul_of_nonneg_left (inv_le_inv₀ (pow_pos hv _) (pow_pos hv _) |>.mpr hl) h0)
    have he :(∑ _ : Fin (n+1),k)=(n+1)*k:=by simp
    have hb := embarkMoney (u:=u) (fun j=> p'.tab ρ v (y j)) x' (fun _=>K) (fun _=>k) hg he.le; rw [he] at hb; apply hb.rise; rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin, Credit.products,Credit.power]; let Q:=(coinMat ((n+1)*k) e)^n; change Q*K^_≤ (T.buy Z)^(n+1)* _*(V^_)⁻¹; unfold K; rw [mul_pow,inv_pow, Nat.mul_comm (n+1) h,pow_mul,mul_comm Q,mul_right_comm _ _ Q] -- fix x^h
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pure_goal ..) (pow_nonneg h0 _)) (inv_nonneg.mpr (pow_nonneg (pow_nonneg hv.le _) _))
end YM.WilsonCoeffUV.Mer.Xa
