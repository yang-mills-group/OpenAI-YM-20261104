import YM.RG12.Alidade.Score
import YM.RG12.Common.Capture
/-! # Price propagation criterion exports the exact coupling-& log-currencies

Interest contract leaves *all* per-cell residual leak for separate treatment. No
claim the achieved per-step omega leaks actually give affordable transport! Use
`interest` ledger: if leaks eventually positive rate O(1/positive spatial log age)
per unit spacing, it can be bought also by a single polynomial in hat. `Near`
already prices losses C/age of that type (on unit spacing or varying spacing with
up to universal C in front of log(L)). Cumulative stage-transition bridging is
explicitly propagated before using this criterion, so doesn't go into the interest
account. Phase/calendar interaction at canonical chart filters not suppressed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Finset Filter RG Wilson Lattice Real Frames Commission
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{M:∀ d,ℕ→RepChart C d}{S:Table C.book}{B:DiffPlan S}
local notation "Z"=> C.path.levels
local notation "χ"=> C.path.levels.clock.hatBeta
local notation "a"=> C.S.a
local notation "clk"=>epoch C.path.levels

-- slightly coarser precision accounting for ease of reuse: hide all terminal conversions in
-- actual polynomial in beta, expose only cumulative interest. Coeff adapter later.
def RightTab (U:ℕ→ℝ)(C:Family G)(S:Table C.book)(M:∀ d,ℕ→RepChart C d)(d:ℕ) : Prop :=
    ∀ x : S.Field d, ∃ p : ℕ, ∀ᶠ k in atTop,∃ v:C.label d,S.project d (M d k v)=x ∧ mass C d v ≤ C.path.levels.clock.hatBeta k ^ p * U k
def RowTab (U:ℕ→ℝ)(C:Family G)(S:Table C.book)(B:DiffPlan S)(M:∀ d,ℕ→RepChart C d) (d w:ℕ):Prop:=
    ∀ L : S.Field d →ₗ[ℂ] ℂ, ∀ h:w≤d,
    (∀ e:ℕ, ∀ he:e<w,∀ x:S.Field e,L (B.rise (he.le.trans h) x)=0) →
    ∃ p:ℕ, ∀ᶠ k in atTop, ∀ v:C.label d, ‖L (S.project d (M d k v))‖ ≤ (C.path.levels.clock.hatBeta k^p * U k)/C.S.a k^(d-w) * mass C d v
variable {V0: ℕ → ℝ}{d w:ℕ}
lemma right_zero (he:RightTab V0 C S M d) {p:ℕ}(hV:∀ᶠ k in atTop,V0 k ≤ χ k^p): RightPrice C S M d:=by
    intro x
    obtain ⟨q,hq⟩:= he x; refine ⟨q+p,?_⟩
    filter_upwards [hV,hq] with k hk h
    obtain ⟨v,he,h⟩:=h
    exact ⟨v,he,h.trans (by rw [pow_add]; exact mul_le_mul_of_nonneg_left hk (pow_nonneg (zero_le_one.trans (delay (Z) _)) _))⟩ -- orientation trans'
lemma row_zero (he:RowTab V0 C S B M d w){p:ℕ}(hV:∀ᶠ k in atTop,V0 k ≤ χ k^p):RowPrice C S B M d w:=by
    intro L H h
    obtain ⟨q,hq⟩:= he L H h; refine ⟨q+p,?_⟩
    filter_upwards [hV,hq] with k hk h v
    apply (h v).trans
    rw [pow_add]; apply mul_le_mul_of_nonneg_right _ (mass_nonneg ..)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk (pow_nonneg (zero_le_one.trans (delay (Z) k)) _)) (pow_nonneg (C.S.a_pos k).le _)

variable {d:ℕ}{V:Grade d→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)][FiniteDimensional ℂ (Col V)]
variable (Y : ℕ → Col V ≃ₗ[ℂ] S.Field d) (P:Col V ≃ₗ[ℂ] S.Field d) (g:ℕ→S.Field d→ℝ)(t e:ℕ→ℝ)(f:ℕ→ℕ)(c:ℕ→Prop)
variable {D Q b r:ℕ}{K:ℝ}
-- Implement local k extraction test at the lit, not needing every off-lit selection
structure Landing (C:Family G) {S:Table C.book}(M:∀ d,ℕ→RepChart C d) (B: DiffPlan S)(Y:ℕ → Col V ≃ₗ[ℂ] S.Field d)(P:Col V≃ₗ[ℂ] S.Field d)(g:ℕ→S.Field d→ ℝ)(t:ℕ→ℝ)(c:ℕ→Prop)(r:ℕ)(K:ℝ):Prop where
   reference (i:Grade d) (x:V i):P (put V i x)∈LinearMap.range (B.rise i.is_le)
   dock: ∀ᶠ i:ℕ in atTop,c i→ C.S.a i ≤ t i ∧ t i ≤ C.S.a i * C.path.levels.clock.hatBeta i^r ∧
           Tests (g i∘Y i) K ∧ ∃ A:Col V→ₗ[ℂ] C.label d, Nonempty (ReadingAt C S d V (g i) i M A r)
variable {Y P g t e f c}
variable (H:Landing C M B Y P g t c r K)
variable (J:Tariff C.path.levels f c Y P t (fun i=>compress (g i∘Y i)) e K D Q b)(hG:G.Simple)(hm:C.Makes){φ:Filter UVIndex}[φ.NeBot](ht:Observing C hm φ M)
local notation "X!"=>engineering (S:=S) M d
lemma pot_price (i j:ℕ)(he:i≤j){e:ℕ→ℝ}{D Q:ℕ}(h:e≥ fun _=>0)(hf:clk i ≤ χ i^2)(hg:G.Simple): pot (Z) D Q e i ≤ χ j^(2*D+Q) * interest e D j:=by
    let Wp (k):=χ k; have hz:=later_rate (C:=C) hg i j he
    have hv:=zero_le_one.trans (delay (Z) j)
    have hl:=pot_big (Z) D Q i h;have he:= outer_big (Z) Q i
    calc pot (Z) D Q e i = clk i^D* outer (Z) Q i * interest e D i:=by unfold pot wallet; ring
         _ ≤ (Wp j ^2)^D * Wp j^Q * interest e D j:=by
            gcongr
            · exact zero_le_one.trans (interest_big h ..)
            · exact zero_le_one.trans (begun (Z) i)
            · exact hf.trans (pow_le_pow_left₀ (year (Z) i).le hz _)
            · exact (outer_hat (Z) Q i).trans (pow_le_pow_left₀ (year (Z) i).le hz _)
            · exact interest_mono h D ‹i≤j›
         _ = _:=by rw [pow_add,pow_mul]

lemma labels_cost {d:ℕ}(q:ℝ)(hq:0≤q)(v:C.label d): mass _ _ ((q:ℂ) • v)=q*mass C d v:=by
   unfold mass Labels.Frame.coeffSize; simp_rw [Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hq]; exact (Finset.mul_sum ..).symm
include J H ht hG hm
set_option maxHeartbeats 500000 in
lemma inward :RightTab (interest e D) C S M d:=by
   intro x
   let i:=Fin.last d
   obtain ⟨c0,hc,hq⟩:= charted (F:=S.Field d) (V:=V) (P:=P) (K:=K) J x 0 (u:=i) i (by simp [prev]) (by intro j hj; exact False.elim (by have h:= j.is_le; change d < j.val at hj; omega))
   -- constants: reading price r twice, year factor p=1 calibration K*C, connector lower cost hat^(d+1) terminal, engineering rebates all horizon
   refine ⟨d+1+r*2+1+(2*D+Q),?_⟩
   have hf : Beacon (Z) f c:= Tariff.beacon (P:=P) J
   filter_upwards [hf.valid,hf.grows.eventually (epoch_enveloped (C.path.levels) hG),hf.grows.eventually hq, hf.grows.eventually H.dock, hf.grows.eventually_ge_atTop (C.ref d), (year_late (Z) hG).eventually_ge_atTop (K^2*c0)] with k hk he hw hg hh hK
   let j:= f k; let y:=χ k; let T:=interest e D k
   obtain ⟨hj,hx,-,h0⟩:= hk
   have ht' := hw hx
   obtain ⟨ha,-,ht1,A,⟨hT⟩⟩:= hg hx
   let p:= X! j
   have hV: g j 0=0:=by simpa [Function.comp] using! ht1.zero
   have hs : Injective (p.comp A):= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun v hv=> norm_le_zero_iff.mp (by have he:= hT.price v; change _ ≤ _ * g j ((p.comp A) v) at he; simpa [hv,hV] using! he)))
   obtain ⟨v,hv⟩:= (show Surjective ((P.symm.toLinearMap.comp p).comp A) from LinearMap.injective_iff_surjective.mp (P.symm.injective.comp hs)) (P.symm x)
   have hP:p (A v)= x := P.symm.injective hv
   obtain ⟨U,hU⟩:= passage hm ht hh hj; let F:=LinearEquiv.ofBijective U (Lamps.inv hU); let u:= F.symm (A v); have hB:U u=A v:=F.apply_symm_apply _
   have hP': X! k u=x:=by
      rw [← hP,← hB]
      have ht:= congr_arg (fun x:C.label d=>S.project d x) (hU.pulls u)
      rw [map_smul,map_smul] at ht
      simpa only [p,engineering_at,Complex.ofReal_pow] using ht.symm
   let l:= (C.S.a k)^d
   refine ⟨(l:ℂ) • u,by rw [map_smul,map_smul]; exact hP',?_⟩
   let b':=compress (g j ∘ Y j);let W:=pot (Z) D Q e j; let w:= (Y j).symm x;let q:=2*D+Q
   have ho:0≤K:=zero_le_one.trans ht1.legal
   have ht₂ := fits_compress ht1; have hw:‖w‖ ≤ K*(c0 * ((y^q)* T)/(t j)^d):=by
      refine (norm_le_coins (b:=b) ht₂ (begun (Z) j) w).trans (mul_le_mul_of_nonneg_left ((ht'.inward).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pot_price j k hj J.losses he hG) hc) (pow_nonneg (J.delays _).le _))) ho)
   have ha':l ≤ t j^d:=pow_le_pow_left₀ (C.S.a_pos k).le ((C.S.strictAnti.antitone hj).trans ha) _
   have hb :0 ≤ y:= (year (Z) k).le; have hr: C.S.a j/C.S.a k ≤ y:= h0.trans (radar_smaller (delay (Z) k) _)
   have hc':(χ j)^r ≤ y^r:=pow_le_pow_left₀ (year (Z) j).le (year_mono (Z) hG hj) _
   have hW : g j x ≤ K*‖w‖:=by have h:= ht1.upper w; dsimp only [Function.comp_apply] at h; exact (Y j).apply_symm_apply x ▸ h
   have hp':‖v‖ ≤ (χ j)^r * (K*‖w‖):=(hT.price v).trans (mul_le_mul_of_nonneg_left (show g j _ ≤ _ from by change g j (p (A v)) ≤ _; rw [hP]; exact hW) (pow_nonneg (year (Z) j).le _))
   have hx : mass C d u ≤ y^(d+1)*(χ j)^r * ‖v‖:=by
      have hd:= hU.lower u; rw [hB] at hd; apply hd.trans;rw [mul_assoc]; exact mul_le_mul (pow_le_pow_left₀ (div_pos (C.S.a_pos _) (C.S.a_pos _)).le hr _) (hT.norm v) (mass_nonneg ..) (pow_nonneg hb _)
   have hT':0 ≤ T:=(exp_pos _).le
   calc
      _ = l*mass C d u := labels_cost l (pow_nonneg (C.S.a_pos k).le _) u
      _ ≤ t j^d * ((y^(d+1)*y^r) *(y^r*(K*(K*(c0*(y^q*T)/(t j)^d))))):=by
         refine mul_le_mul ha' (hx.trans ?_) (mass_nonneg ..) (pow_nonneg (J.delays _).le _)
         have he : 0 ≤ y^r:=pow_nonneg hb _; have hm:0 ≤ y^(d+1):=pow_nonneg hb _
         refine mul_le_mul (mul_le_mul_of_nonneg_left hc' hm) (hp'.trans (mul_le_mul hc' (mul_le_mul_of_nonneg_left hw ho) (mul_nonneg ho (norm_nonneg _)) he)) (norm_nonneg _) (mul_nonneg hm he)
      _ = y^(d+1+r*2)*(K^2*c0)*(y^q*T):= by
         have hz: (t j)^d ≠ 0:= (pow_pos (J.delays _) _).ne'; simp only [pow_add,pow_mul]; field_simp
      _ ≤ y^(d+1+r*2)*y*(y^q*T):=by apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (pow_nonneg hb _)) (mul_nonneg (pow_nonneg hb _) hT')
      _ = _:=by rw [pow_add (χ k) _ (2*D+Q),pow_succ]; unfold T q y; ring

lemma outward (w:ℕ): RowTab (interest e D) C S B M d w:=by
   intro L hw hL
   let u:Grade d := ⟨w,Nat.lt_succ_of_le hw⟩
   have hx :∀ v∈prev V u,L (P v)=0:=by
      intro v hv
      rw [← by_grade V v,map_sum,map_sum]; apply sum_eq_zero;intro i _
      rcases le_or_gt u i with hi|hi
      · rw [hv i hi]; simp [put]
      have h:i.val<w:=hi
      obtain ⟨v,hv⟩:= H.reference i (v i); rw [← hv]; exact hL i.val h v
   obtain ⟨c0,hc,hq⟩:= charted (F:=S.Field d) (V:=V) (P:=P) (K:=K) J (0:S.Field d) L (u:=Fin.last d) u hx (by simp)
   let E:=d*(b+1); let q:=2*D+Q; let o:=1+(1+r)*w+q+2*E+r+1
   refine ⟨o,?_⟩
   have hf : Beacon (Z) f c:= Tariff.beacon (P:=P) J
   filter_upwards [hf.valid,hf.grows.eventually (epoch_enveloped (C.path.levels) hG),hf.grows.eventually hq, hf.grows.eventually H.dock, hf.grows.eventually_ge_atTop (C.ref d), (year_late (Z) hG).eventually_ge_atTop (c0*(↑(d+1:ℕ))*K^2)] with k hk he ht' hg hh hK x
   let j:= f k; let y:=χ k; let T:=interest e D k
   obtain ⟨hj,hx,-,h0⟩:= hk
   have ht' := ht' hx
   obtain ⟨-,ha,ht1,A,⟨hT⟩⟩:= hg hx
   let p:= X! j
   obtain ⟨U,hU⟩:=passage hm ht hh hj
   let F:=S.project d (M d k x)
   let v:=(Y j).symm (X! k x)
   have hy : Y j v = X! k x:= (Y j).apply_symm_apply _
   have hx':X! k x = p (U x):=by
      have ht:= congr_arg (fun x:C.label d=>S.project d x) (hU.pulls x)
      rw [map_smul,map_smul] at ht
      simpa only [p,engineering_at,Complex.ofReal_pow] using! ht.symm
   have ha' : C.S.a j/C.S.a k ≤ y := h0.trans (radar_smaller (delay (Z) k) _); have hZ :(χ j)^r ≤ y^r:= pow_le_pow_left₀ (year (Z) j).le (year_mono (Z) hG hj) _
   have ht'': t j ≤ C.S.a k*y^(1+r):=by
      have hB : C.S.a j ≤ y * C.S.a k:= (div_le_iff₀ (C.S.a_pos k)).mp ha'
      exact ha.trans ((mul_le_mul hB hZ (pow_nonneg (year (Z) j).le r) (mul_nonneg (year (Z) k).le (C.S.a_pos _).le)).trans_eq (by rw [pow_add,pow_one]; ring))
   have hs:0≤ K:=zero_le_one.trans ht1.legal
   have hv : ‖v‖ ≤ K*(y^r*y)*mass C d x:=by
      have he:=ht1.lower v;dsimp only [Function.comp_apply] at he; rw [hy,hx'] at he
      apply he.trans
      rw [mul_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hs
      exact (hT.look (U x)).trans (mul_le_mul hZ ((hU.norms x).trans (mul_le_mul_of_nonneg_right ha' (mass_nonneg _ _ _))) (mass_nonneg ..) (pow_nonneg (year (Z) k).le _))
   let hd:=(↑(d+1:ℕ):ℝ); have hI:0 ≤ hd:=by unfold hd; positivity
   have hb:= fits_compress ht1
   have hT':0 ≤ T:=(exp_pos _).le; have he':0 ≤ y:=(year (Z) k).le; have ha0:= (C.S.a_pos k).le
   have hS₀:=zero_le_one.trans (begun (Z) j)
   have hr : ‖L (X! k x)‖ ≤ (y^o*T)*(C.S.a k)^w * mass C d x:=by
      rw [← hy]; have h1:=ht'.outwards v
      apply h1.trans
      have hl:clk j ≤ y^2:=he.trans (pow_le_pow_left₀ (year (Z) j).le (year_mono (Z) hG hj) _)
      calc
        _ ≤ c0*((C.S.a k*y^(1+r))^w) * ((y^q*T)*(hd*K*(y^2)^E*(K*(y^r*y)*mass C d x))):=by
           apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (J.delays _).le ht'' _) hc)
           · apply mul_le_mul (pot_price j k hj J.losses he hG)
             · apply ((coins_trim hb hS₀ ..).trans (coins_le hb (begun (Z) j) v)).trans
               exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS₀ hl _) (mul_nonneg hI hs)) hv (norm_nonneg _) (mul_nonneg (mul_nonneg hI hs) (pow_nonneg (sq_nonneg y) _))
             · exact coins_nonneg hb hS₀ _
             exact mul_nonneg (pow_nonneg he' _) hT'
           · exact mul_nonneg (zero_le_one.trans (pot_big (Z) D Q j J.losses)) (coins_nonneg hb hS₀ _)
           exact mul_nonneg hc (pow_nonneg (mul_nonneg ha0 (pow_nonneg he' _)) _)
        _ = (c0*(↑(d+1:ℕ))*K^2)*(y^((1+r)*w+q+2*E+r+1)*T)*C.S.a k^w*mass C d x:=by simp only [pow_add,pow_mul,mul_pow,pow_one,hd]; ring
        _ ≤ y*(y^((1+r)*w+q+2*E+r+1)*T)*(C.S.a k)^w*mass C d x:=by
           have hv:=mass_nonneg _ _ x; gcongr
        _ = _:=by unfold o;rw [show 1+(1+r)*w+q+2*E+r+1=1+((1+r)*w+q+2*E+r+1) by omega,pow_add y 1,pow_one]; ring
   have ha :=C.S.a_pos k
   rw [engineering_at,map_smul,norm_smul,Complex.norm_real, Real.norm_of_nonneg (pow_nonneg ha.le d)] at hr -- rewrites all d trouble! 
   rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha _)]
   apply le_of_mul_le_mul_left _ (pow_pos ha w)
   rw [show a k ^ d=(a k^w)*(a k^(d-w)) from by rw [←pow_add]; congr 1; omega] at hr
   convert hr using 1 <;> first | rfl | ring
end YM.RG12.Alidade
