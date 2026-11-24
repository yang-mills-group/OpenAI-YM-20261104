import YM.SignedWilsonExpansion.F9.Lantern
/-!
# Engineering shrink of separated steps. θ geometry. Charges upper power budget before 
   certifying F9 estimates. Paths at K compare unencoded and paid ranks with shrinks.

No replacing N clock with M in these movements. Mass spans REAL marks; port returns true
 names.Bound polynomial by ψ on (1+Z). Geometry contact cross-town only by `physical.Course`.
-/
set_option autoImplicit false
set_option maxHeartbeats 840000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r p u n :ℕ}
variable {B Q D Z X Y η t a ρ d:ℝ}{E W U:Credit}
def sizeT (A:Levels G)(ρ:ℝ)(m:ℕ):= A.S.a m /ρ
local notation "δ"=> sizeT A ρ
variable {R:Realm G (e+1) E}
section
variable (A:Levels G)(w:0<ρ)
include w
lemma sizeT_pos (m):0<sizeT A ρ m:= div_pos (A.S.a_pos _) w
lemma anti_sizeT : Antitone (sizeT A ρ):=fun i j p=> div_le_div_of_nonneg_right (A.S.strictAnti.antitone p) w.le
lemma repr_step (i):sizeT A ρ i=(A.S.block i).val*sizeT A ρ (i+1):=by unfold sizeT; rw [← mul_div_assoc,A.S.a_step]; field_simp
end

abbrev SpanR (A:Levels G)(ρ d:ℝ)(i:ℕ):ℝ:= d/sizeT A ρ i
variable {x:ℕ→Fin (n+1)→Cover} 
-- notation shadow.Coherence
lemma reprClear (A:Levels G){ρ d:ℝ} (w:0<ρ)(h:0<d):0<SpanR A ρ d i:= div_pos h (sizeT_pos A w i)

-- quote stand.Always budget full p-rank at clock actual positions.
def taxesR (d Z B:ℝ)(a:Fin (n+1)→ℝ)(D:Fin (n+1)→ℕ)(u:ℕ)(E W:Credit):ℝ:= (∏ i,a i)*(d^u)⁻¹ * (B^(u-∑ i,D i)) * ((E.powC (∑ i,D i)).buy Z*(W.powC (n+1)).buy Z)
def ped (A:Levels G)(ρ:ℝ)(a:Fin (n+1)→ℝ)(D:Fin (n+1)→ℕ)(B:ℝ)(i:ℕ)(j: Fin (n+1)):ℝ:= B*(a j*(sizeT A ρ i ^ D j)⁻¹)
lemma taxes_nn {a:Fin (n+1)→ℝ}{d Z B:ℝ}(w:0<d)(p:1≤Z)(v:0≤B)(hv:∀ i, 0≤ a i)(D:Fin (n+1)→ℕ)(u)(E W:Credit) : 0 ≤ taxesR d Z B a D u E W:= mul_nonneg (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _=>hv i) (inv_nonneg.mpr (pow_nonneg w.le _))) (pow_nonneg v _)) (mul_nonneg (zero_le_one.trans (Credit.purchase _ p)) (zero_le_one.trans (Credit.purchase _ p)))
lemma taxation (E W:Credit)(R:Realm G (e+1) E)(q:Canopy R m c Z)(p:m ≤ i)(u':i<c)
    {ρ d:ℝ}(v:0<ρ)(w:0<d)(a:Fin (n+1)→ℝ)(D:Fin (n+1)→ℕ) (hm:(∑ i,D i)≤ u)(h:∀ i,0≤ a i):
      ((SpanR R.draws ρ d i)^u)⁻¹*(∏ j, ped R.draws ρ a D (W.buy Z) (i+1) j) ≤ taxesR d Z (sizeT R.draws ρ m) a D u E W:=by
    let A:=R.draws; let δi:= sizeT A ρ i; let δ':=sizeT A ρ (i+1); let H:= sizeT A ρ m; let x':ℝ:=(A.S.block i).val; let T:=∑ i,D i; let A':=∏ i,a i; let C:=(W.buy Z)^(n+1)
    have g:0<δ':=sizeT_pos A v _; have he:0<δi:= sizeT_pos A v _; have hf:δi=x'*δ':=repr_step A v _; have ho:1≤Z:=q.positive; have hW:0≤C:=pow_nonneg (zero_le_one.trans (W.purchase ho)) _; have ha:0≤A':=Finset.prod_nonneg fun i _=>h i; have hT:0<(d^u)⁻¹:=by positivity
    have hx:0≤x':= Nat.cast_nonneg _; have hv:δi≤ H:= anti_sizeT A v p; have hu:0≤δi^(u-T):=pow_nonneg he.le _; have hh:= mul_nonneg ha hT.le
    have leg : ((d/δi)^u)⁻¹ = (δi^u)*(d^u)⁻¹:=by rw [div_pow, inv_div,div_eq_mul_inv] -- syntax ambiguous
    have hc : δi^u*(δ'^T)⁻¹= δi^(u-T)*x'^T:=by nth_rw 1 [← show u-T+T=u from Nat.sub_add_cancel hm, pow_add]; rw [mul_assoc]; apply congr_arg (HMul.hMul (δi^(u-T))); rw [hf, mul_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ g.ne'),mul_one]
    unfold taxesR; rw [Credit.power,Credit.power]
    change _≤ A'*(d^u)⁻¹ * H^(u-T)*((E.buy Z)^T*C)
    calc
       _ = (δi^u*(d^u)⁻¹) * (C*(A'*(δ'^T)⁻¹)):=congrArg₂ _ leg (by
          simp only [ped,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]; rfl)
       _ = A'*(d^u)⁻¹ * δi^(u-T)*(x'^T*C):=by
          rw [show δi^u*(d^u)⁻¹ * (C*(A'*(δ'^T)⁻¹)) = (A'*(d^u)⁻¹*C)*(δi^u*(δ'^T)⁻¹) by ring,hc];ring
       _ ≤ _:=mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he.le hv _) hh) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx ((R.taxes i (q.arch.trans p)).height.trans (q.older E p u'.le)) T) hW) (by positivity) (mul_nonneg hh (pow_nonneg (he.le.trans hv) _))
lemma risePed (u:0<ρ)(q:0≤B)(p:m≤ i)(a:Fin (n+1)→ℝ)(D:Fin (n+1)→ℕ)(hv:∀ i,0≤a i):ped A ρ a D B m≤ ped A ρ a D B i:=fun j=> mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (inv_le_inv₀ (pow_pos (sizeT_pos _ u m) _) (pow_pos (sizeT_pos _ u i) _) |>.mpr (pow_le_pow_left₀ (sizeT_pos _ u i).le (anti_sizeT A u p) _)) (hv j)) q
lemma Jetty.engine (W:Credit)(q:Canopy R m c Z) (hρ:0<ρ)(hd:0<d)(C:Cowrie R.draws m c x (SpanR R.draws ρ d)) (a:Fin (n+1)→ℝ)(D:Fin (n+1)→ℕ) (P:ℕ→Fin (n+1)→Era G ℝ) (hm:(∑ i,D i)≤u)(h:∀ i,0≤a i)(s:∀ i,m≤ i→i<c→∀ j, P i j=verseI R.draws R.paid i N k (P (i+1) j))(w:∀ i,m≤ i→i≤ c→∀ j, Respect k e u 1 (P i j) (ped R.draws ρ a D (W.buy Z) i j)):
    Jetty (fun _:Fin (n+1)=>k) R.draws R.paid m c N x u e P (taxesR d Z (sizeT R.draws ρ m) a D u E W):=
    C.entry _ w (fun _ _ _=> risePed hρ (zero_le_one.trans (W.purchase q.positive)) (Nat.le_succ _) _ _ h) s (fun i p t=>taxation E W R q p t hρ hd a D hm h)

-- appointments bought ≤ maximal halo.Z.Sync
namespace Stair
variable {F:Frames G}{A':Council F}{L:TowerP F}(p':Stair A' L A Ñ m c N h p k u X)(H:Hol G)
local notation "H'"=> (F.level h)
variable (s':0<ρ)
def lightFee (H:Hol G)(F:Frames G)(Q:Council F)(h k u e:ℕ) : Credit:= ((stationed H F Q h k u e).choose).plus Credit.leanC
include H
include p'
lemma budget (w:m≤ i)(v:i≤c): Palette (F.level h) (p'.ladder i) k u p ((lightFee H F A' h k u p).buy X):= ((stationed H F A' h k u p).choose_spec L A Ñ m c N X p' i w v).money (Credit.thickens _ (p'.charm h le_rfl).pos)
-- in unencoded units
omit H in
def tab (ρ:ℝ)(t:ℕ)(y:(F.level h).Index): Era G ℝ:= ((sizeT A ρ t)^(wt H' y))⁻¹ • p'.ladder t y
include s'
lemma tab_meter (w:m≤ i)(v:i≤c)(j:(F.level h).Index) : Respect k p u 1 (p'.tab ρ i j) (((lightFee H F A' h k u p).buy X)* (((sizeT A ρ i)^(wt H' j))⁻¹)):=by
    let p₀:= p'.budget H w v; let B:= (lightFee H F A' h k u p).buy X; unfold tab; let x:=(sizeT A ρ i)^(wt H' j); have ht:0≤ x:=pow_nonneg (sizeT_pos A s' i).le _
    rw [mul_comm]
    exact ((show Respect k _ u 1 (p'.ladder i j) _ from ⟨p₀.field _,fun i v r _=> p₀.fee j i r v⟩).series x⁻¹).rise (le_of_eq (by rw [abs_of_nonneg (inv_nonneg.mpr ht)]))
lemma transmit (w:m≤ i)(v:i<c)(j:(F.level h).Index): p'.tab ρ i j=verseI A Ñ i N k (p'.tab ρ (i+1) j):=by
    unfold tab; have b:=w.trans (Nat.le_succ i); have hb:= p'.charm h le_rfl; let K : Era G ℝ→ Era G ℝ := verseI A Ñ i N k; let Q:= p'.ladder (i+1) j; have ht:Auth k Q:= p'.funding H b v j; have he:∀ x:ℝ,K (x • Q)= x • K Q := fun x=> by simpa only [Finset.sum_singleton] using verse_sum A (Ñ:=Ñ) hb.simple (v.trans_le hb.cap) hb.ratios (P:=fun _=>Q) (S:={()}) (fun (_:Unit) _=> ht) (fun _=>x)
    let δ':=sizeT A ρ (i+1); let x:ℝ:=(A.S.block i).val; have hx:0<x:= Nat.cast_pos.mpr (A.S.block _).pos; have hf:0<δ':=sizeT_pos _ s' _; rw [p'.step w v]; change ((sizeT A ρ i^ (wt H' j))⁻¹ • (x^(wt H' j) • K Q))=K ((δ'^ (wt H' j))⁻¹ • Q); rw [he _, smul_smul,repr_step A s',mul_pow]; refine congr_arg (· • K Q) ?_; change (x^_*δ'^_)⁻¹ * x^_= _; field_simp
end Stair
end YM.WilsonCoeffUV.Mer.Xa
