import YM.SchemeRG11.Banner.Moon
/-! Volume-passing. Engineering singularity power weights controlled separately. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Banner
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels MvPolynomial Outlook North Long
open scoped Classical Pointwise
variable {G:Gauge}{n d:ℕ} {T:Align.Itinerary} {B:Window}{x u:ℤ}{R r:ℝ} {f:Ban G}
lemma ozone(T:Align.Itinerary)(g:Slate){s:ℕ→Finset Cover} (h:Plain T (-4) g)(hg:∀ᶠ i in atTop,∀p∉s i,g i p=0)(hw:Surround (T:=T) s R) : Tendsto (fun i=>T.gap i* (∑ p∈s i,g i p)) atTop (𝓝 0):=by
 obtain ⟨C,hC,H⟩:= h.1; let U:Slate:=fun i p=> (T.gap i)^(-3:ℤ)*g i p
 have he:∀ᶠ i in atTop,∀p∉s i,U i p=0:=hg.mono fun i hi p hp=>by unfold U; rw [hi p hp,mul_zero]
 have hy:∀ᶠ i in atTop,∀ p∈s i, |U i p| *baseU T i p^3 ≤ C:=by
    filter_upwards [H] with i hi p hp; have hx:=T.positive i;have hh:=World.d_pos p
    refine le_trans (b:= C*(World.d p)^((-1):ℤ)) ?_ ?_
    · unfold U baseU; rw [abs_mul,abs_of_pos (by positivity)]
      apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hi p trivial) (by positivity)) (by positivity)); apply le_of_eq; rw [zpow_zero, zpow_neg, zpow_neg, zpow_neg]; norm_num; field_simp -- check
    rw [zpow_neg,zpow_one]; calc _≤ C*1 := by gcongr; apply inv_le_one_of_one_le₀ (World.d_le _)
                                 _ = C:= by rw [mul_one]
 have hb(y:E4)(hy:y≠0): Tendsto (fun i=>U i (stake (T.gap i) y)) atTop (𝓝 (0:ℝ)):=by
    obtain ⟨c,hc⟩:= h.2 y hy trivial _ (follows y)
    have H:= T.cutoff.mul hc; rw [zero_mul] at H; apply H.congr; intro i; have hh: T.gap i≠0:=(T.positive i).ne'; change _*_ = T.gap i ^ (-3:ℤ)*_; rw [←mul_assoc, show T.gap i*T.gap i^(-4:ℤ)=T.gap i^(-3:ℤ) from ?_]
    rw [zpow_neg,zpow_neg]; field_simp
 have ht:= climbers (g:=fun _=>0) he hC.le hw hy hb; rw [integral_zero] at ht; apply ht.congr; intro i; unfold U; rw [← Finset.mul_sum,← mul_assoc]; congr 1; have he:=T.positive i; rw [zpow_neg]; field_simp
lemma trace_grid (T:Align.Itinerary)(g:Slate){s:ℕ→Finset Cover}(h:Plain T u g)(hs:Surround (T:=T) s R)(hp:∀ᶠ i in atTop,∀p∉s i,g i p=0)(hr:r>0) (he:∀ᶠ i in atTop,∀p,Near T r i p→ g i p=0): Finishes (fun i=>T.gap i ^ (u+4)*(∑p∈s i,g i p)):=by
 let C:=max (|R| +1) (r+1); have hc:r≤C:=le_trans (by linarith) (le_max_right ..)
 let f:Slate:=fun i p=>T.gap i^u*g i p
 have H:∃ A>0,∀ᶠ i in atTop,∀p ∈s i, |f i p| * (baseU T i p)^3 ≤ A:=by
    let x := u+3
    have hi(t:ℝ)(ht:r≤t∧ t≤C):t^x ≤ C^x+r^x:=by
       have hpos : t>0:=hr.trans_le ht.1
       by_cases h:x≥0
       · exact (zpow_le_zpow_left₀ h hpos.le ht.2).trans (le_add_of_nonneg_right (by positivity))
       have hG:= zpow_le_zpow_left₀ (show 0≤ -x by omega) hr.le ht.1
       rw [zpow_neg,zpow_neg, inv_le_inv₀ (by positivity) (by positivity)] at hG; exact hG.trans (le_add_of_nonneg_left (zpow_pos (hr.trans_le hc) _).le)
    obtain ⟨B,hB,b⟩:=h.wall; refine ⟨B*(C^x+r^x),mul_pos hB (add_pos (zpow_pos (hr.trans_le hc) x) (by positivity)),?_⟩
    filter_upwards [b,he,hs] with i h hb HS p w; by_cases hQ:Near T r i p
    · simp only [f,hb p hQ,mul_zero,abs_zero,zero_mul]; exact mul_nonneg hB.le (add_nonneg (zpow_pos (hr.trans_le hc) x).le (by positivity))
    unfold f; have hk :baseU T i p>0:=mul_pos (T.positive _) (World.d_pos _); rw [abs_mul,abs_of_pos (zpow_pos (T.positive _) _)]; refine le_trans (b:=B*baseU T i p^x) ?_ ?_
    · apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h p trivial) (zpow_pos (T.positive i) _).le) (by positivity)); refine le_of_eq ?_; rw [show x=u+(3:ℕ) from rfl,zpow_add₀ hk.ne',zpow_natCast]; unfold baseU; rw [mul_zpow,zpow_zero];ring
    apply mul_le_mul_of_nonneg_left _ hB.le; exact hi _ ⟨le_of_lt (lt_of_not_ge hQ), (HS p w).trans (le_trans (le_trans (le_abs_self _) (by linarith)) (le_max_left ..))⟩
 obtain ⟨A,hA,H⟩:=H
 have htop:∀ᶠ i in atTop,∀p∉s i,f i p=0:=hp.mono fun i h p hp=>by unfold f; rw [h _ hp,mul_zero]
 convert travellers htop hA.le hs H (fun y hy=> h.2 y hy trivial _ (follows y)) using 1
 funext i; unfold f; rw [← Finset.mul_sum,zpow_add₀ (T.positive _).ne', ← mul_assoc]; rw [mul_comm (T.gap i ^ u)]; rfl

lemma skimP {p:pLabel G}{a:Size G n}(h:IsWeightedHomogeneous generation p d)(hb:B.rOut< R) (hg: bill a≤(d:ℤ)): Tendsto (fun i=> T.gap i * coeff a (inlay G n (nebula (cove T B i) (gateY T R i) p))) atTop (𝓝 0):=by
 have he : Sigil T n ((d:ℤ)+4) (smoke T B p):= swell (crystalline T G n) h B
 let s:= scriptum n (smoke T B p) a
 have hp:Plain T (-4) s:=(he.key a).widened (by omega)
 have hz:∀ᶠ i in atTop,∀ p∉gateY T R i,s i p=0:=(banished hb p).mono fun i hi x hx=>by unfold s scriptum; rw [hi _ hx,map_zero,coeff_zero]
 simp_rw [frameB, map_add,map_sum, coeff_add, coeff_sum, mul_add]
 let Z:= coeff a (inlay G n ((Atoll.land G).heat (castFirst 1 p)))
 have ht:= (T.cutoff.mul_const Z).add (ozone T s hp hz (gate_d ..)); rw [zero_mul,add_zero] at ht; exact ht
lemma fateful {p:pLabel G}(h:IsWeightedHomogeneous generation p d)(hb:B.rOut<R) (a:Size G n){θ:Cover→G.Color}{m:ℕ}(he:θ ∈ cap G.Color (m+1)): Finishes (fun i=>T.gap i ^ (bill a+(m:ℤ)-(d:ℤ))*coeff a (inlay G n (gas (cove T B i) (gateY T R i) p θ))) :=by
 let q:= flash T B θ p; have H:Sigil T n ((d:ℤ)+(4-(m:ℤ))) q:=driveP (crystalline T G n) θ he p h _
 let f:= scriptum n q a
 have hu:∀ᶠ i in atTop,∀ x∉gateY T R i,f i x=0:=(cold_out hb θ p).mono fun i h x hx=>by unfold f scriptum q; rw [h x hx,map_zero,coeff_zero]
 obtain ⟨r,hr,A⟩:= cold_in T B θ p
 have hQ:∀ᶠ i in atTop,∀x,Near T r i x→f i x=0:=A.mono fun i hi x hx=>by unfold f scriptum q; rw [hi x hx,map_zero,coeff_zero]
 rw [show bill a+(m:ℤ)-(d:ℤ)= (bill a-((d:ℤ)+(4-(m:ℤ))))+4 by abel]; simp_rw [sparked,map_sum,coeff_sum]; exact trace_grid T f (H.key a) (gate_d ..) hu hr hQ
end YM.SchemeRG11.Banner
