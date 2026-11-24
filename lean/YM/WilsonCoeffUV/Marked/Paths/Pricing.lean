import YM.WilsonCoeffUV.Marked.Paths.PostRank
/-! Entire grade forecast, leftover and release. May be re-chosen *before* a step.
 For actual local comparison RG02 must transport the actual weighted E through
 mask and representative differences. Does not assert equality on different real labels.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{k h r t i j e m b:ℕ}{s v u A B:ℝ}
variable {V W I α β:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]

-- Define bound independent of Vs to pre-schedule. exclusive grade.
def bruise (G:Gauge)(k i e:ℕ)(s:ℝ):ℝ:=∑ j∈ Finset.range (k+e+1), ∑ r:Fin (k+i+1), flour G (steep s) r j
lemma bruise_nn (G:Gauge)(k i e:ℕ)(s:ℝ):0≤bruise G k i e s:=Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> flour_nn ..
lemma skyps (P:RailsP G k i V)(p:tintR P s A)(h:0<s) (e:ℕ): Rain (linesR P).2 e (steep s) (bruise G k i e s*A):=by
   have he:= mul_nonneg (bruise_nn G k i e s) p.1; refine ⟨he,fun j t z=>?_⟩
   by_cases b:z<k+e+1; · apply (sky_pay P p h j z).cost; apply mul_le_mul_of_nonneg_right _ p.1; unfold bruise; apply Finset.single_le_sum (f:=fun _=> _) _ (Finset.mem_range.mpr b); intro l _; exact Finset.sum_nonneg fun _ _=> flour_nn ..
   rw [(starR _ p h).coverN j z (by omega)]; exact Cork.zero.cost he

lemma ladder' (G:Gauge)(k e i:ℕ)(x:i < e)(s:ℝ)(hp:0<s) : ∃ C:ℝ,∃ u:ℝ,0<u∧0≤C ∧ ∀ (V:Type)[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V] (P:Bookend V G)(A),Nimbus k e P → Rain P e s A →(∀ j< i,P j=0) → tintR (shelfM P i k) u (C*A):=by
    obtain ⟨u,p,hv⟩:= annual hp G k i; let B (r:Fin (k+i+1)):= christmas G s r; let C:=∑ j,B j; have hb j:0≤ B j:=christmas_pos G s hp _
    have hc:0≤ C:= Finset.sum_nonneg fun i _=> hb i
    refine ⟨C,u,p,hc,fun V _ _ _ P A q r _=>?_⟩; let Y:=shelfM P i k
    refine ⟨mul_nonneg hc r.1,fun b=>⟨shadest _ (q.hue _ x b),?_⟩⟩; apply Work.F08.budget_minor (cap_raise (floatPrice (r.2 i x b) hp) (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> hb i) (Finset.mem_univ b)) r.1)) (fun j=> ink_pos (Y b j)); intro j; exact bend_in _ (hv b)

/-- Indexed staging fields. Even dictionary for passive grade tags beyond cap (no bounds on those). -/
abbrev Robes (G:Gauge)(V:Type)(k:ℕ) := (i:ℕ)→ RailsP G k i V
def baton (P:Robes G V k)(i:ℕ): Era G V:= ∑ j∈Finset.range i, linesR (P j)
def Rains (T:Robes G V k)(i:ℕ)(s C:ℝ): Prop:=0≤C ∧ ∀ j< i,tintR (T j) s C
omit [CompleteSpace V] in
lemma Rains.slack {R:Robes G V k}(h:Rains R i s A)(hp:u ≤ s)(hx:A ≤ B): Rains R i u B:= ⟨h.1.trans hx,fun n t => tintR.flex (h.2 n t) hp hx⟩
lemma sufficesR {R: Robes G V k}(h:Rains R i s A)(hp:0<s): Auth k (baton R i) := Auth.sum fun i hi=>starR _ (h.2 i (Finset.mem_range.mp hi)) hp
lemma mooring {R: Robes G V k}(h:Rains R i s A)(hp:0<s)(n:Side)(j t): (baton R i).1 n j t= plume ((baton R i).2 j t) n := by
   induction i generalizing n j t with
   | zero=> simp [baton,plume_zero]
   | succ i ih=>
      have hz : Rains R i s A:=⟨h.1,fun _ t=> h.2 _ (Nat.lt_succ_of_lt t)⟩
      rw [baton,Finset.sum_range_succ]; exact carousel (sufficesR hz hp) (starR _ (h.2 _ i.lt_succ_self) hp) (ih hz) (tintR.flare _ (h.2 _ i.lt_succ_self) hp) n j t

def clothing (G:Gauge)(k i e:ℕ)(s:ℝ):ℝ:=∑ j∈ Finset.range i, bruise G k j e s
lemma clothing_nn (G:Gauge)(k i e:ℕ)(s:ℝ): 0≤clothing G k i e s:= Finset.sum_nonneg fun _ _=> bruise_nn ..
lemma scheduleD {R:Robes G V k} (h:Rains R i s A)(hp:0<s)(e:ℕ): Rain (baton R i).2 e (steep s) (clothing G k i e s*A):=by
    refine ⟨mul_nonneg (clothing_nn ..) h.1,fun j t l=>?_⟩; simp only [baton,Prod.snd_sum,Finset.sum_apply]; rw [clothing,Finset.sum_mul]; apply Cork.sum; intro i hi; exact (skyps (R i) (h.2 i (Finset.mem_range.mp hi)) hp e).2 j t l

-- allow repricing in changing grade emission V without extra curvature

noncomputable def climbSteps (P:Bookend V G)(R:Robes G V k)(t i:ℕ) : Robes G V k:= match i with
| 0=> R
| i+1=> let L:= climbSteps P R t i
        Function.update L (t+i) (shelfM (P - (baton L (t+i)).2) (t+i) k)
omit [CompleteSpace V] in
lemma ladderC {R:Robes G V k}{X:RailsP G k i V}: baton (Function.update R i X) (i+1)= baton R i + linesR X:=by
    unfold baton; rw [Finset.sum_range_succ,Function.update_self]; apply congr_arg₂ (·+·) _ rfl; exact Finset.sum_congr rfl fun j z=> by rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp z))]
lemma buildC (G:Gauge)(k t m e:ℕ)(h:t+m ≤ e)(s:ℝ)(hs:0<s): ∃ v:ℝ,∃ C:ℝ,0<v∧ v≤ s∧1≤ C∧ ∀ (V:Type)[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V](P:Bookend V G)(R:Robes G V k)(A), Nimbus k e P→ Rain P e s A → Rains R t s A→(∀ j< t,(baton R t).2 j=P j) →
    let T:= climbSteps P R t m; Rains T (t+m) v (C*A) ∧ (∀ j< t+m,(baton T (t+m)).2 j=P j) ∧ ∀ j< t,T j=R j:=by
    induction m with
    | zero=>
       refine ⟨s,1,hs,le_rfl,le_rfl,fun V _ _ _ P R A _ _ u t=>by simp only [one_mul,Nat.add_zero]; exact ⟨u,t,fun _ _=>rfl⟩⟩
    | succ m ih=>
       obtain ⟨w,B,u,hv,hP,hQ⟩:= ih (by omega); let i:=t+m; have hx:i< e:=by omega
       have ha:0<steep w:=div_pos u (by norm_num); have hw:steep w≤w:= (show w/4≤w from by linarith)
       let X:=clothing G k i e w; have hh:0≤X:=clothing_nn ..; let Y:=1+X*B
       have hy:1≤Y:= le_add_of_nonneg_right (mul_nonneg hh (zero_le_one.trans hP))
       obtain ⟨C,b,p,q,u'⟩:= ladder' G k e i hx (steep w) ha; let v:= min b w; let W:=max B (C*Y); have hz:B≤ W:=le_max_left ..; have hi:0<v:=lt_min p u
       refine ⟨v,W,hi,(min_le_right ..).trans hv,hP.trans hz,?_⟩; intro V _ _ _ P R A S g K M O
       obtain ⟨hR,hL,d⟩:=hQ V P R A S g K M
       let L:= climbSteps P R t m; let F:=P-(baton L i).2
       have hE: Nimbus k e F:= twilit S (nimb _ (sufficesR hR u) _)
       have hG: Rain F e (steep w) (Y*A):= by
           have he:= scheduleD hR u e; have hp:= Rain.less P g (hw.trans hv) le_rfl
           refine ⟨mul_nonneg (zero_le_one.trans hy) g.1,fun j y r=>?_⟩
           apply ((hp.2 _ y r).sub (he.2 _ y r)).cost; apply le_of_eq; unfold Y X i; ring
       have hD j (x:j< i): F j=0:=by unfold F; rw [Pi.sub_apply,hL j x,sub_self]
       let z:= shelfM F i k; have hN:tintR z b (C*(Y*A)):= u' V F _ hE hG hD
       let H : Robes G V k:= Function.update L i z
       have hX : H= O:=rfl
       rw [← hX, show t+(m+1)=i+1 from Eq.symm (Nat.add_assoc ..)]
       have hA:= mul_nonneg (zero_le_one.trans (hP.trans hz)) g.1
       refine ⟨⟨hA,fun j α=>?_⟩,fun j α=>?_,fun j α=>?_⟩
       · unfold H; by_cases e:j=i; · subst j; rw [Function.update_self]; apply hN.flex (min_le_left ..); rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) g.1
         rw [Function.update_of_ne e]; exact (hR.slack (u:=v) (min_le_right ..) (mul_le_mul_of_nonneg_right hz g.1)).2 j (show j< i from by omega)
       · unfold H; rw [ladderC]; simp only [Prod.snd_add,Pi.add_apply]; by_cases z':j=i; · subst j; rw [(ladderM G k e i hx _ ha).choose_spec.choose_spec.2.2 F _ hE hG hD|>.2]; unfold F; rw [Pi.sub_apply, add_sub_cancel]
         rw [leant _ (show j< i from by omega),add_zero]; exact hL j (by change j< i; omega)
       unfold H; rw [Function.update_of_ne (show j≠i from by unfold i; omega)]; exact d j α
end YM.WilsonCoeffUV.Mer.Rolls
