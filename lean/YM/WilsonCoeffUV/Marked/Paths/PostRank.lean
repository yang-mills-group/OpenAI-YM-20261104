import YM.WilsonCoeffUV.Marked.Paths.WardNull
/-!
# Universal-by-rank rooted path forecast permits all lower-grade changes
 paid through stated horizon with linear cost in same moment units. Caller
 doesn't inherit narrower widths next step: primary NIMBUS inputs and
 Cork and σ-stage, including repeated stable kernels, are on held cover.
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{k h r t i j e m b:ℕ}{s u A B:ℝ}
variable {V W I α β:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]

-- one palette for each finite grade/rank bundle
abbrev RailsP (G:Gauge)(k:ℕ)(i:ℕ)(V:Type):= (r:Fin (k+i+1))→ RadP G r.val→Comet G V r.val

def tintR (P:RailsP G k i V) (s A:ℝ):Prop:=0≤A ∧ ∀ r,(∀ x,shadeStar (P r x)) ∧ SumBudget (fun j=>integerP (P r j) s) A
def linesR (P:RailsP G k i V): Era G V:= ∑ r,bolus (P r) i
open Work.F08
lemma cap_raise {f:I→ℝ}(p:SumBudget f A)(e:A≤ B): SumBudget f B:=⟨p.1,p.2.1,p.2.2.trans e⟩
omit [CompleteSpace V] in
lemma tintR.flex {C:RailsP G k i V}(p:tintR C s A)(h:u ≤ s)(v:A ≤ B): tintR C u B:= ⟨p.1.trans v,fun r=>⟨(p.2 r).1,(budget_minor (cap_raise (p.2 r).2 v) (fun j=>ink_pos (C r j)) (fun j=>bend_in (C r j) h))⟩⟩
lemma starR (P:RailsP G k i V)(h:tintR P s A)(p:0<s): Auth k (linesR P):= Auth.sum (fun r (_:r∈Finset.univ)=> Mer.Rolls.stars p (h.2 r).2 (Nat.le_of_lt_succ r.isLt) (h.2 r).1)
-- any extension wraps directly
lemma carousel {P T:Era G V}(p:Auth k P)(q:Auth k T)(h:∀ n i j,P.1 n i j=plume (P.2 i j) n)(v:∀ n i j,T.1 n i j=plume (T.2 i j) n)(n:Side)(i j): (P+T).1 n i j=plume ((P+T).2 i j) n:=by
    obtain ⟨s,a,hs,c⟩:=(p.wing i j).land; obtain ⟨t,f,ht,g⟩:=(q.wing i j).land; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply,h,v,plume_add c g hs ht]
lemma tintR.flare (P:RailsP G k i V)(h:tintR P s A)(p:0<s)(n:Side)(j z): (linesR P).1 n j z= plume ((linesR P).2 j z) n:=by
    simp only [linesR,Prod.fst_sum,Prod.snd_sum,Finset.sum_apply]; rw [plume_spurs _ (X:=fun r=>A*flour G (steep s) r.val z) (fun r _=>(show Cork Bank.terrain 0 (steep s) _ _ from sky_high p (h.2 r).2 _ _ _)) (show 0<steep s from div_pos p (by norm_num))]; rfl
-- prices from finite forecast; min choose across heights/widths
omit [CompleteSpace V] in
lemma sky_pay (P:RailsP G k i V)(h:tintR P s A)(p:0<s)(j z): Cork Bank.terrain 0 (steep s) ((∑ r:Fin (k+i+1), flour G (steep s) r z)*A) ((linesR P).2 j z):=by
    unfold linesR; simp only [Prod.snd_sum, Finset.sum_apply]; rw [mul_comm _ A, Finset.mul_sum]; apply Cork.sum; intro i _; exact sky_high p (h.2 i).2 _ _ _

def Rain (P:Bookend V G)(e:ℕ)(s A:ℝ): Prop:=0≤A ∧ ∀ i<e,∀ j,Cork Bank.terrain 0 s A (P i j)
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma Rain.less (P:Bookend V G)(h:Rain P e s A)(v:u≤ s)(g:A≤B): Rain P e u B:=⟨h.1.trans g,fun i hi j=> ((h.2 i hi j).mono v).cost g⟩
lemma rain_step (G:Gauge)(k i e:ℕ)(s:ℝ):∃ C:ℝ,0≤ C∧∀ (P:RailsP G k i V)(A),tintR P s A→0<s→ Rain (linesR P).2 e (steep s) (C*A) := by
    let Z (j:ℕ):=∑ r:Fin (k+i+1), flour G (steep s) r j; have hz j: 0≤ Z j:= Finset.sum_nonneg (fun _ _=>flour_nn ..)
    let L:= Finset.range (k+e+1); refine ⟨∑ j∈ L,Z j,Finset.sum_nonneg (fun i _=>hz i),fun P A h p=>?_⟩; have hp:= (starR P h p).coverN
    have hv:0≤ (∑ j∈L,Z j)*A:=mul_nonneg (Finset.sum_nonneg fun i _=> hz i) h.1
    refine ⟨hv,fun i hi j=>?_⟩; by_cases H:j∈ L; · exact (sky_pay P h p i j).cost (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>hz i) H) h.1)
    rw [hp i j (by unfold L at H; have he:=mt (Finset.mem_range).mpr H; omega)]; exact Cork.zero.cost hv

def shelfM (P:Bookend V G)(i k): RailsP G k i V:=fun r=> meteor (P i r.val)
lemma christmas_pos (G:Gauge)(s:ℝ)(p:0<s)(i:ℕ):0≤christmas G s i:=by
    unfold christmas; apply mul_nonneg (by positivity); apply mul_nonneg (ceilPoly_pos ..).le; by_cases h:i=0; · simp [h,tiePay]
    exact pow_nonneg (boardPay_nn (by apply div_pos; · linarith
                                      positivity)) _
lemma annual (p:0<s)(_G:Gauge)(k i:ℕ) : ∃ v:ℝ,0<v ∧∀ r: Fin (k+i+1),v ≤ humidity s r:=by
    let r:=k+i; refine ⟨humidity s r, mist p _,fun k=>?_⟩; unfold humidity; gcongr; exact Nat.le_of_lt_succ k.isLt
omit [CompleteSpace V] in
lemma leant (P:RailsP G k j V)(p:i< j): (linesR P).2 i=0:=by unfold linesR; simp only [Prod.snd_sum, Finset.sum_apply]; exact Finset.sum_eq_zero fun _ _=> prior_m _ p
lemma ladderM (G:Gauge)(k e i:ℕ)(x:i < e)(s:ℝ)(hp:0<s):∃ C:ℝ,∃ u:ℝ,0<u∧0≤C ∧ ∀ (P:Bookend V G)(A),Nimbus k e P → Rain P e s A →(∀ j< i,P j=0) →
    tintR (shelfM P i k) u (C*A) ∧ (linesR (shelfM P i k)).2 i=P i:=by
    obtain ⟨u,p,hv⟩:= annual hp G k i; let B (r:Fin (k+i+1)):= christmas G s r; let C:=∑ j,B j; have hb j:0≤ B j:=christmas_pos G s hp _
    have hc:0≤ C:= Finset.sum_nonneg fun i _=> hb i
    refine ⟨C,u,p,hc,fun P A q r h=>?_⟩; let Y:=shelfM P i k; have hx: tintR Y u (C*A):=by
       refine ⟨mul_nonneg hc r.1,fun b=>⟨shadest _ (q.hue _ x b),?_⟩⟩; apply budget_minor (cap_raise (floatPrice (r.2 i x b) hp) (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> hb i) (Finset.mem_univ b)) r.1)) (fun j=> ink_pos (Y b j)); intro j; exact bend_in _ (hv b)
    refine ⟨hx,?_⟩; funext j; change (linesR Y).2 i j= _; by_cases z:j<k+i+1
    · let b:Fin (k+i+1):=⟨j,z⟩
      have he: (bolus (Y b) i).2 i j=P i j:= flowing _ (r.2 i x j) hp (q.lead _ x _) (q.hue _ x _) (nymph q x h) _
      unfold linesR; rw [Prod.snd_sum,Finset.sum_apply,Finset.sum_apply, Finset.sum_eq_single b]; exact he
      · intro t _ ht; exact latter_m (Y t) (fun e=> ht (Fin.ext e))
      simp
    rw [q.shell _ x j (by omega)]; exact (starR _ hx p).coverN i j (by omega)
-- Wisps in next
end YM.WilsonCoeffUV.Mer.Rolls
