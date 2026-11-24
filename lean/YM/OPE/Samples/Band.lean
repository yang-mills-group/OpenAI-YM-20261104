import YM.OPE.Samples.Lead
/-!
# Windows in which captures live with polynomial credit
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter Finset Lattice RG Wilson Polar MeasureTheory
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C: Family G}{I L J:Type}[Fintype I][DecidableEq I]{i j k:I}{Q:Rhythm I} {H t u v w n A:ℕ} {f:Filter L}
    {T:L→ℝ}{R r s: L→ℕ→ℝ} {α:ℕ→ℝ}{q e a b : L→ℝ}
set_option quotPrecheck false
-- Order data. Tops include all radius upper caps used at that layer.
structure Border (f:Filter L)(T:L→ℝ)(n:ℕ)(R r :L→ℕ→ℝ)(α:ℕ→ℝ) : Prop where
    life : Tendsto T f atTop
    pace t: t≤n→0 ≤ α t ∧ α t ≤ 1
    narrows t:t ≤ n→ Tendsto (fun i=> R i t) f (𝓝 0)
    rates t:t ≤ n→ RateIs f T (fun i=> r i t) (-α t)
    relative t:t ≤ n→ValueStamp f T (fun i=> R i t / r i t)
    narrow t:t ≤ n→ ∀ᶠ i in f,r i t ≤ R i t
    leap t:t < n → ∀ p:ℕ, Tendsto (fun i=> R i (t+1)/r i t*T i^p) f (𝓝 0)
namespace Border
variable (B: Border f T n R r α)
include B
lemma ahead (h:t ≤ n): RateIs f T (fun i=> R i t) (-α t):=by
    have hh:= B.rates t h; apply ((hh.mul (B.relative t h|>.zeroCost B.life)).swap (add_zero _)).congr; filter_upwards [hh.pos] with i hi; field_simp
lemma before (h:t ≤ n): Tendsto (fun i=> r i t) f (𝓝 0):= squeeze_zero' ((B.rates t h).pos.mono fun i hi=> hi.le) (B.narrow t h) (B.narrows _ h)
lemma negligible (h:t < n)(hw:Wallet f T q): Tendsto (fun i=>R i (t+1)/r i t*q i) f (𝓝 0):=by
    obtain ⟨p,hp⟩:=hw; apply tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) _ (B.leap t h p)); filter_upwards [hp,(B.ahead h).pos,(B.rates t h.le).pos] with i hp hR hr; rw [norm_mul, Real.norm_of_nonneg (div_pos hR hr|>.le)]; exact mul_le_mul_of_nonneg_left hp (div_pos hR hr|>.le)
lemma tiny (h:t < u)(he:u ≤ n): ∀ᶠ i in f,R i u < r i t:= by
    have ht (i:ℕ)(ht:i < n) : ∀ᶠ j in f,R j (i+1) < r j i:=by filter_upwards [(B.rates i ht.le).pos, (B.leap i ht 0).eventually (gt_mem_nhds zero_lt_one)] with j he hv using (div_lt_one he).mp (by simpa only [pow_zero,mul_one] using hv)
    induction u with
    | zero=>omega
    | succ v ih=> rcases eq_or_lt_of_le (show t ≤ v by omega) with h|h; subst t; exact ht v he; filter_upwards [ih h (by omega), B.narrow v (by omega), ht v he] with i hi he hh using hh.trans_le (he.trans hi.le)
lemma in_order (h:t ≤ u)(he:u ≤ n) : ∀ᶠ i in f,r i u ≤ r i t ∧ R i u ≤ R i t:=by rcases h.lt_or_eq with h|rfl; filter_upwards [B.tiny h he,B.narrow _ he,B.narrow _ (h.le.trans he)] with i hi hu ht using ⟨hu.trans hi.le,hi.le.trans ht⟩; exact Eventually.of_forall fun _=>⟨le_rfl,le_rfl⟩
lemma costs (hw:ValueStamp f T (fun i=> a i/r i t))(hz:ValueStamp f T (fun i=> b i/R i t))(h:t ≤ n) : ValueStamp f T (fun i=> b i/a i):=by
    apply (((hz.div hw).mul (B.relative t h))).congr; filter_upwards [(B.rates t h).pos,(B.ahead h).pos] with i he hi
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; rw [show b i*(R i t)⁻¹*(r i t*(a i)⁻¹)*(R i t*(r i t)⁻¹)= b i*(a i)⁻¹ * (R i t*(R i t)⁻¹)*(r i t*(r i t)⁻¹) by ring, mul_inv_cancel₀ he.ne',mul_inv_cancel₀ hi.ne',mul_one,mul_one]
lemma diverge (hw:Wallet f T (fun i=> r i t/a i))(hz:Wallet f T (fun i=> b i/R i (t+1)))(h:t<n) : Tendsto (fun i=>b i/a i) f (𝓝 0):=by
    apply (B.negligible h (hw.mul hz)).congr'; filter_upwards [(B.rates t h.le).pos,(B.ahead h).pos] with i he hi
    simp only [div_eq_mul_inv]; rw [show R i (t+1)*(r i t)⁻¹*(r i t*(a i)⁻¹*(b i*(R i (t+1))⁻¹))= b i*(a i)⁻¹ * (R i (t+1)*(R i (t+1))⁻¹)*(r i t*(r i t)⁻¹) by ring, mul_inv_cancel₀ he.ne',mul_inv_cancel₀ hi.ne',mul_one,mul_one]
end Border
open Rhythm
local notation "μ" => C.S.a
variable (D:L→Loom Q) {P:ℝ} -- extent factor E
structure Oscars (B:Border f T Q.limit R r α) (P:ℝ)(D:L→Loom Q)(C: Family G) : Prop where
    lower t:t ≤ Q.limit→ Height C.S f T (fun i=>(D i).below t) (α t)
    upper t:t ≤ Q.limit→ Height C.S f T (fun i=>(D i).launch t) (α t)
    grab t:t ≤ Q.limit→ ∀ᶠ i in f,P*R i t ≤ C.S.a ((D i).below t+1)
    loggap t:t ≤ Q.limit→ ValueStamp f T (fun i=> C.S.a ((D i).below t)/R i t)
    toll t:t ≤ Q.limit→ValueStamp f T (fun i=> C.S.a ((D i).launch t)/r i t)
    meter t:t ≤ Q.limit→ ∀ᶠ i in f,C.S.a ((D i).launch t) < r i t/T i^32
variable {D}
namespace Border
variable {W r' D'}(P':LogPackage C W r' D')
    (B:Border f T n R r α)
include B P'
lemma two (he:t ≤ n)(hp: 1 ≤ P) : ∃ m j : L→ℕ, Height C.S f T m (α t) ∧ Height C.S f T j (α t) ∧ ValueStamp f T (fun i=> C.S.a (m i)/R i t) ∧ ValueStamp f T (fun i=> C.S.a (j i)/r i t) ∧ ∀ᶠ i in f,P* R i t ≤ μ (m i+1) ∧ μ (j i)< r i t/T i^32 ∧m i+1< j i:=by
    have hh:=B.life; let M i:= P* R i t; let J i:= r i t/T i^32; have hP:0<P:= zero_lt_one.trans_le hp
    have hD:= B.ahead he; obtain ⟨m,hm,hU,hm'⟩:= bracket_down hh ( ((RateIs.const hh hP).mul hD).swap (zero_add _)) (show Tendsto M f (𝓝 0) from (by simpa only [mul_zero] using! (B.narrows t he).const_mul P)) P'
    have hz:= B.rates t he; have hX:= (ValueStamp.atT hh).pow hh 32; obtain ⟨j,hj,hY,hj'⟩ := bracket_up hh ((hz.div (hX.zeroCost hh)).swap (sub_zero _)) (show Tendsto J f (𝓝 0) from by apply squeeze_zero' _ _ (B.before he); filter_upwards [hz.pos,hX.profit] with i hi hp using (div_pos hi hp).le; filter_upwards [hz.pos,hh.eventually_ge_atTop 1] with i hi hT using div_le_self hi.le (one_le_pow₀ hT)) P'
    refine ⟨m,j,hm,hj, (hm'.inv.mul (ValueStamp.const hh hP)).congr ?_,(hj'.inv.div hX).congr ?_,?_⟩
    · filter_upwards [hD.pos] with i hi; rw [inv_div]; field_simp
    · filter_upwards [hz.pos,hh.eventually_gt_atTop 0] with i hi hp; rw [inv_div]; field_simp
    filter_upwards [hU,hY,hh.eventually_ge_atTop 1,hz.pos,hD.pos,B.narrow t he] with i hU hY hh hz hR h; exact ⟨hU,hY.1,C.S.strictAnti.lt_iff_gt.mp (hY.1.trans_le ((div_le_self hz.le (one_le_pow₀ hh)).trans (h.trans ((le_mul_of_one_le_left hR.le hp).trans hU))))⟩
omit B P'
private def always (Q: Rhythm I) : Loom Q:= ⟨fun i=>4*i,fun i=>4*i+3,fun i _=>by omega,fun i _=>by omega⟩
lemma prizes (P':LogPackage C W r' D')(B:Border f T Q.limit R r α)(hp:1 ≤ P): ∃ D:L→Loom Q,Oscars B P D C:=by
    -- replace general B from include? use variable name different
    choose m j hm hj hD hE hY using fun i (hi:i ≤ Q.limit)=> Border.two P' B hi hp -- arg order
    let a i l:= if h:l ≤ Q.limit then m l h i else 0; let b i l:=if h:l≤ Q.limit then j l h i else 0
    let p i:= ∃ S:Loom Q,S.below=a i∧ S.launch=b i; have hz : ∀ᶠ i in f,p i:=by
       have hh:∀ k (hk:k< Q.limit), ∀ᶠ i in f,j k hk.le i < m (k+1) hk i:=by
          intro k hk
          filter_upwards [(B.diverge (a:=fun i=>μ (j k hk.le i)) (b:=fun i=>μ (m (k+1) hk i)) (show Wallet f T _ from ((hE k hk.le).inv).up.congr (Eventually.of_forall (fun i=>inv_div ..))) (hD _ hk).up hk).eventually (gt_mem_nhds zero_lt_one)] with i hi using C.S.strictAnti.lt_iff_gt.mp ((div_lt_one (C.S.a_pos _)).1 hi)
       filter_upwards [(eventually_all_finset (Iic Q.limit)).mpr (fun l h=>eventually_all.mpr (fun e:l≤ Q.limit=> hY l e)),(eventually_all_finset (Iic Q.limit)).mpr (fun l h=>eventually_all.mpr (hh l))] with i hA hB
       refine ⟨⟨a i,b i,fun l hl=> ?_,fun l hl=>?_⟩,rfl,rfl⟩
       · unfold a b; rw [dif_pos hl,dif_pos hl]; exact (hA l (mem_Iic.mpr hl) hl).2.2
       unfold a b; rw [dif_pos (show l+1 ≤ Q.limit from hl),dif_pos hl.le]; exact hB l (mem_Iic.mpr hl.le) hl -- order
    let S i:=if h:p i then h.choose else always Q
    have he(l)(hl:l≤Q.limit): ∀ᶠ i in f,(S i).below l=m l hl i ∧ (S i).launch l=j l hl i:=by
       filter_upwards [hz] with i hi; unfold S; rw [dif_pos hi,hi.choose_spec.1,hi.choose_spec.2]; exact ⟨dif_pos hl,dif_pos hl⟩
    refine ⟨S,?_⟩; constructor
    · intro l hl; have ht:=(he l hl); exact ⟨(hm l hl).grows.congr' (ht.mono fun _ hh=>hh.1.symm), (hm l hl).pace.congr' (ht.mono fun x hh=> by dsimp only; rw [hh.1])⟩
    · intro l hl; have ht:=(he l hl); exact ⟨(hj l hl).grows.congr' (ht.mono fun _ hh=>hh.2.symm), (hj l hl).pace.congr' (ht.mono fun x hh=> by dsimp only; rw [hh.2])⟩
    · intro l hl; filter_upwards [he l hl,hY l hl] with i hi he; rw [hi.1]; exact he.1
    · intro l hl; exact (hD l hl).congr ((he l hl).mono fun x hh=> by dsimp only; rw [hh.1])
    · intro l hl; exact (hE l hl).congr ((he l hl).mono fun x hh=> by dsimp only; rw [hh.2])
    intro l hl; filter_upwards [he l hl,hY l hl] with i hi he; rw [hi.2]; exact he.2.1
end Border
end YM.OPE.Log.Trunk
