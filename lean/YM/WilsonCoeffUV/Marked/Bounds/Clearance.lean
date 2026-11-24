import YM.WilsonCoeffUV.Product.Report.Age
import YM.WilsonCoeffUV.Marked.Bounds.OneMarch
/-!
# Fk bounds ABOVE OPEN (A mesh candidate)

Roll recursion with no interacting mask. High interval retains all mixed
histories but used/small on the same-label allowed assignments. This is a
fixed finite marker demand and angular order. Geometry grows exponentially
with log age, traversal proof retains old lengths. Top mixed in log start
zero. All-singleton stability input uses separate sharper controls, supplied
for model columns as a theorem after.
 -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost Real
open scoped Topology BigOperators
variable {c f:Side}{ι α U V t:Type}{J J' S' K I T:Finset ι}{D k:ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}

noncomputable def carrierR (S:Schedule)(m:ℕ)(x:ℕ)(p:Cover): Cover:= if _h:m<x then match x with | 0=>p | j+1=> carrierR S m j (parentC (S.block j) p) else p
termination_by x
lemma nearR (S:Schedule)(m:ℕ): carrierR S m m=id:=funext fun _=>by rw [carrierR,dif_neg (lt_irrefl _)]; rfl
lemma upR (S:Schedule)(a:m≤ i)(v:Cover): carrierR S m (i+1) v=carrierR S m i (parentC (S.block i) v):=by rw [carrierR,dif_pos (by omega)]
lemma farD (S:Schedule)(x:m≤ i)(p q:Cover)(u:ρ+12≤Bank.terrain.gap (carrierR S m i p) (carrierR S m i q)): ρ *Real.exp (snowP S m i)+12 ≤ Bank.terrain.gap p q:=by
   induction i,x using Nat.le_induction generalizing p q with
   | base=> rwa [nearR,show snowP S m m=0 from sub_self _,exp_zero,mul_one] at *
   | succ i hv ih=>
       rw [upR S hv,upR S hv] at u
       let L:= S.block i; have he:= ih _ _ u; have ht:(L.val:ℝ)*Bank.terrain.gap (parentC L p) (parentC L q)≤ Bank.terrain.gap p q + 8*L.val:= by exact_mod_cast parent_stride p q (L:=L)
       unfold snowP at *; rw [Schedule.scale_succ,add_sub_right_comm,exp_add, exp_log (by positivity)]
       have hU:(3:ℝ)≤ L.val:=by exact_mod_cast S.block_large i
       dsimp only [L] at *; nlinarith [mul_le_mul_of_nonneg_left he (show (0:ℝ)≤ ((S.block i).val:ℝ) by positivity)]

def cleared (S:Schedule)(m i:ℕ)(ρ:ℝ)(p:ι→Cover)(J: Finset ι):Prop:=∀ u∈ J,∀ t∈ J,u≠t→ρ+12 ≤ Bank.terrain.gap (carrierR S m i (p u)) (carrierR S m i (p t))
lemma rimD {p:ι→Cover} {S:Schedule}(v:cleared S m i ρ p J)(u:m ≤ i)(g:1<J.card)(x:dock Cover α r): ρ*Real.exp (snowP S m i) ≤ Syn Bank.terrain p J x:=by
    obtain ⟨a,ha,b,hb,h⟩:= Finset.one_lt_card.mp g; let X:=foyer p J x; have he:=farD S u _ _ (v _ ha _ hb h); have hz: Bank.terrain.gap (p a) (p b) ≤ Syn Bank.terrain p J x:= leg_le _ X (.inl ⟨_,ha⟩) (.inl ⟨_,hb⟩); linarith only [he,show ((Bank.terrain.gap (p a) (p b)):ℝ) ≤ Syn Bank.terrain p J x from Nat.cast_le.mpr hz]

lemma est_cost {E V:Credit}{R:Realm G (e+1) E}(v:R.anchor≤m)(p:m≤ i)(t:R.y m≤ z): R.cash V i ≤ V.buy (z+snowP R.draws.S m i):=
   V.elder (R.depth _ (v.trans p)) ((R.age _ _ v p).trans (add_le_add_left t _))
def elabC (E:Credit):Credit:= (Credit.leanC.plus E)
lemma plusA {E:Credit}{R:Realm G (e+1) E}(v:R.anchor≤m)(p:m≤ i)(t:R.y m≤z): z+snowP R.draws.S m (i+1)≤ (elabC E).buy (z+snowP R.draws.S m i):=by
   let S:=R.draws.S; have hz:1≤z:= (R.depth _ v).trans t; have hp:0≤snowP S m i:=sub_nonneg.mpr (scales _ p); let x:=z+snowP S m i; have ht:1≤x:= le_trans hz (le_add_of_nonneg_right hp)
   apply le_trans _ (Credit.fuel Credit.leanC E ht); rw [Credit.lean_cost]; have hf: ((S.block i).val:ℝ)≤ E.buy x:= (R.taxes i (by omega)).height.trans (est_cost v p t); have he:= Real.log_le_sub_one_of_pos (x:=((S.block i).val:ℝ)) (by positivity); change z+snowP S m (i+1)≤ _; change _≤ z+snowP S m i+E.buy x; unfold snowP; linarith only [S.scale_succ i,hf,he]

variable [DecidableEq ι]
lemma heldR (A:Levels G)(z:ι→ Cover)(p:cleared A.S m i ρ z J)(x:J'⊆ J)(u:m≤ i)(w:backRow (ll A i).L S'): cleared A.S m (i+1) ρ (splitQ (ll A i) z S' w) J':=by
    intro a ha j hj f; have ht a : parentC (A.S.block i) (splitQ (ll A i) z S' w a)=z a:= parent_pack (L:=A.S.block i) (α:=Unit) ((z a, inflate (ll A i) S' w a,()))
    rw [upR _ u, upR _ u, ht,ht]; exact p a (x ha) j (x hj) f

variable {K':ι→ℕ}[Fintype ι]{E W U':Credit}{R:Realm G (e+1) E}
def iceBill (G:Gauge)(D k K:ι→ℕ)(e:ℕ)(B U E:Credit):= ((tollStep G D k K e U E).prodC (B.usingC (elabC E))).powC (Fintype.card ι)
-- fixed CR requirement on opening separation, in z. NOT claiming chosen on actual C,f.
def galeGate (G:Gauge)(D k K:ι→ℕ)(e:ℕ)(B U E:Credit)(z:ℝ):= 2*(iceBill G D k K e B U E).behind.buy z*U.behind.buy z
def penaltyB (U:Credit)(z ρ v:ℝ) := ρ/(2*U.behind.buy z)*exp (v/8)
omit [DecidableEq ι] [Fintype ι] in
lemma betweenK {p:ι→Cover}{X:Ten V (Cloth α) j}[NormedAddCommGroup V](u:Wig Bank.terrain p τ g J X){z:ℝ}(x:∀ m:dock Cover α j, (τ-σ)*Syn Bank.terrain p J m ≥ 2*z)(h:g≤exp z):Wig Bank.terrain p σ (exp (-z)) J X:=by
    refine ⟨(Real.exp_pos _).le,fun m=>(u.2 m).trans ?_⟩; apply (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le).trans; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith [x m]
lemma freezing (p:Cloze D k R U')(h:R.anchor≤m)(v:R.y m≤z)(u:m≤ i)(ρ:ℝ)(g:galeGate G D k K' e W U' E z≤ ρ) (X: Ten V (Cloth α) j) [NormedAddCommGroup V]{y:ι →Cover}(q:cleared R.draws.S m i ρ y J)(hp:1< J.card)(ht:Wig Bank.terrain y (elixir (R.mint i (h.trans u)).gear) ((R.cash (tollStep G D k K' e U' E) i* W.buy (z+snowP R.draws.S m (i+1)))^J.card) J X): Wig Bank.terrain y (R.mint i (h.trans u)).σ (exp (- penaltyB U' z ρ (snowP R.draws.S m i))) J X:=by
    let S:=R.draws.S; let β:= snowP S m i; let I:= (R.mint i (h.trans u)).gear; let w:=elixir I-I.σ; let B':=W.usingC (elabC E); let K:= tollStep G D k K' e U' E; let T:= iceBill G D k K' e W U' E; let L:=T.behind.buy z; let ψ:= U'.behind.buy z; let F:= exp (β/8); let φ:=penaltyB U' z ρ β
    have hz:1≤z:= (R.depth _ h).trans v; have he:=plusA h u v; have hw:0<w:=sub_pos.mpr (pureEl _); have hu:0≤β:=sub_nonneg.mpr (scales _ u); have hβ:1≤z+β:=hz.trans (le_add_of_nonneg_right hu); have hQ:1≤ z+snowP S m (i+1):=hz.trans (le_add_of_nonneg_right (sub_nonneg.mpr (scales _ (by omega))))
    let y':=z+β; let c:=R.cash K i; let C:= W.buy (z+snowP S m (i+1))
    have hV:1≤C:=W.purchase hQ; have hv:1≤c:=K.purchase (R.depth _ (h.trans u)); let X':=c*C; have ht':1≤X':= one_le_mul_of_one_le_of_one_le hv hV; have hX: X'^J.card≤ T.buy y':=by
        have H:C≤B'.buy y':=by unfold B'; rw [Credit.stock_up]; exact W.elder hQ he
        unfold T iceBill; rw [Credit.power,Credit.products]; refine (pow_le_pow_right₀ ht' (Finset.card_le_univ _)).trans (pow_le_pow_left₀ (zero_le_one.trans ht') (show X'≤K.buy y'* _ from mul_le_mul (est_cost h u v) H (zero_le_one.trans hV) (zero_le_one.trans (K.purchase hβ))) _)
    have hψ:0<ψ:=zero_lt_one.trans_le (U'.behind.purchase hz)
    have hL:1≤L:=T.behind.purchase hz
    have hρ: 2*L*ψ≤ρ:=g; have h0:0≤ρ:= le_trans (mul_nonneg (by linarith) hψ.le) hρ
    have hf: 0 < F:= exp_pos _
    refine betweenK ht (fun x=>?_) (le_trans hX ?_)
    · have hT:= rimD q u hp x; have hx: w⁻¹ ≤ ψ*F:= (p.heat _ (h.trans u)).trans ((est_cost h u v).trans (prices_t U' hz hu))
      change 2*φ≤w*_
      have hφ: 2*φ≤ w*(ρ*exp β):=by
          have hb: φ≥0:=by unfold φ penaltyB; change 0 ≤ ρ/(2*ψ)*F; positivity
          rw [← div_le_iff₀' hw]; refine le_trans (b:=2*φ*(ψ*F)) (by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hx (by positivity)) ?_
          unfold φ penaltyB; have hv': 2*(ρ/(2*ψ)*F)*(ψ*F)=ρ*(F*F):=by field_simp
          rw [hv']; unfold F; rw [← Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) h0
      exact le_trans hφ (mul_le_mul_of_nonneg_left hT hw.le)
    change _≤exp φ; apply le_trans (prices_t T hz hu); have hW : L*F≤φ:=by
        unfold φ penaltyB; change L*F ≤ ρ/(2*ψ)*F; exact mul_le_mul_of_nonneg_right ((le_div_iff₀ (by positivity)).mpr (by linarith only [hρ])) hf.le
    linarith only [hW,Real.add_one_le_exp φ,show L*F=T.behind.buy z*exp (β/8) from rfl]
end YM.WilsonCoeffUV.Wheel.Mark
