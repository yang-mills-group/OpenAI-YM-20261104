import YM.MSbar.Sage.Coarse
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V U' V' :Config G n}{x: Site n}{R: Rep G n}{σ C T a v δ w β:ℝ}
open Finset RG.PathData
variable {Y X: Support n}{k M:ℕ}
open AnalyticBridge.VerifiedReset Next.Scheduling Precision
-- ordinary fd reconnection derived not from seeded reach but actual edges.
def ringed (Y:Support n):Finset (Edge (Site n)):=univ.filter fun i=> i.1∈Y ∨ i.1+step i.2∈Y
lemma foggy (h: Spine Y U V) (e : Edge (Site n)) (he:e∉ringed Y) : U e=V e:=by
    have hp: e.1∉Y ∧ e.1+step e.2∉Y:=by simpa [ringed] using he
    exact h {e.1,e.1+step e.2} (by simp [hp.1,hp.2]) e (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
lemma blue (Y: Support n): (ringed Y).card ≤ Y.card*8 :=by
    let v:=Y ×ˢ (Finset.univ:Finset Axis); apply (Finset.card_le_card (t:= (show Finset (Edge (Site n)) from v)∪ v.image (fun i=>(i.1-step i.2,i.2))) ?_).trans (Finset.card_union_le .. |>.trans ?_)
    · rintro ⟨i,j⟩ hi; rcases (mem_filter.mp hi).2 with hp|hp; exact mem_union_left _ (mem_product.mpr ⟨hp,mem_univ _⟩); refine mem_union_right _ (mem_image.mpr ⟨(i+step j,j),mem_product.mpr ⟨hp,mem_univ _⟩,?_⟩); dsimp only; rw [add_sub_cancel_right]
    apply (Nat.add_le_add_left (show (v.image (fun i=>(i.1-step i.2,i.2))).card ≤ v.card from card_image_le) v.card).trans
    · unfold v; simp only [card_product,card_univ]; simp [Axis]; omega
lemma tally (h:Spine Y U V)(F: Config G n→ℝ) (hp:∀ (p : Edge (Site n))(V : Config G n)(b:G.El),|F V-F (update V p b)| ≤ a) (ha:0≤ a) : |F U-F V| ≤ (Y.card*8:ℝ)*a :=by
    have h (s:Finset (Edge (Site n))) (U V: Config G n) (hh:∀ i,i∉s → U i=V i) : |F U-F V| ≤ (s.card:ℝ)*a:=by
       induction s using Finset.induction generalizing U V with
       | empty=> rw [show U=V from funext fun i=> hh i (by simp)]; simp
       | insert i s he ih=>
         let X:=update U i (V i); have hg : |F X-F V| ≤ (s.card:ℝ)*a := ih X V fun j hi=> by by_cases hx:j=i; subst j; simp [X]; unfold X; rw [update_of_ne hx]; exact hh j (by simp [hx,hi])
         rw [show F U - F V=(F U-F X)+(F X-F V) by abel,card_insert_of_notMem he]; push_cast; linarith only [abs_add_le (F U-F X) (F X-F V), hg, (show |F U-F X| ≤ a from hp i U (V i))]
    exact (h (ringed Y) U V (foggy ‹Spine ..›)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast blue Y) ha)
variable (hp:Place Y M U U' V V' R.p.threshold)
    (h:R.Lawful σ C T δ w)(hk:R.p.B≤ M)(hd:Decent R.clip R.p)(hz:0≤ R.beta)
local notation "Wc"=> R.path.inChannels R.clip R.p R.beta
include h hk hd hz
private lemma lp (p:Edge (Site n))(V:Config G n)(b:G.El): |(∑ i:Site n, RG.PathData.atomSeries R.path.loop R.p V i)-(∑ i: Site n, RG.PathData.atomSeries R.path.loop R.p (update V p b) i)| ≤ T*R.p.threshold^2*(2* Real.exp (σ*8)*(81*meter σ)):=by
    have hh i:= atomic R.path.loop R.p i (stitch p V b) h.paths.width h.paths.two
    rw [←sum_sub_distrib]; apply (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i (_:i∈univ)=> hh i)).trans ?_); rw [← mul_sum,← mul_sum]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (radial _ h.paths.width p.1) (by positivity)) (mul_nonneg (budget_nonneg h.paths.two) (sq_nonneg _))
def outset (p: BudgetPoint)(σ C δ T β:ℝ)(M y:ℕ):= craft C σ β y M+(y*8:ℝ)*(T*p.threshold^2*(2* Real.exp (σ*8)*(81*meter σ))+life p δ)
include hp
lemma formal_edge : |R.exponent U-R.exponent V+R.beta*(mainTerm R.clip R.path U'-mainTerm R.clip R.path V')| ≤ outset R.p σ C δ T R.beta M Y.card:=by
   have ht :0≤ T:=budget_nonneg h.paths.two; let y(W : Config G n)(s : Signed):=R.path.principal R.clip R.p R.beta (pull s 0 W)
   let f(W : Config G n)(s : Signed):= regularP (pull s 0 W) R.path R.clip
   let b:=(16*C^2); let q(V:Config G n):=∑ i, RG.PathData.atomSeries R.path.loop R.p V i
   let m:= (Y.card*8:ℝ); let d:= craft C σ R.beta Y.card M; let k:=T*R.p.threshold^2*(2*Real.exp (σ*8)*(81*meter σ)); have hx :0≤ k:= by unfold k; have hi := meter_pos h.paths.width; positivity
   have H₀(i): |y U i-y V i-R.beta*(f U' i-f V' i)| ≤ d+m*k:=by
      have hh:=place_oriented hp i; have h := bud hh h.paths hk hd hz; let P:= q (pull i 0 U)- q (pull i 0 V); let D:= y U i-y V i-R.beta*(f U' i-f V' i)
      have hv:= tally hh.old q (lp (R:=R) ‹R.Lawful σ C T δ w› hk hd hz) hx -- arguments
      have he : (harp i Y).card=Y.card:=card_image_of_injective _ (Equiv.injective _)
      rw [he] at h hv; change |P| ≤ _ at hv; change |D| ≤ _; have hi : |D-P| ≤ d:=by
           convert h using 2; unfold D P q y f; abel
      rw [show D=D-P+P by abel]; exact (abs_add_le ..).trans (add_le_add hi hv)
   let M':=(Wc U)-(Wc V)-R.beta*(mainTerm R.clip R.path U'-mainTerm R.clip R.path V')
   let c:=(Fintype.card Signed:ℝ); have hc:0<c:=by unfold c; positivity
   have h0:M' = c⁻¹*∑ i,(y U i-y V i-R.beta*(f U' i-f V' i)):=by unfold M' inChannels mainTerm RG.Patch.average; rw [sum_sub_distrib,sum_sub_distrib,←mul_sum,sum_sub_distrib]; unfold c y f regularP; ring -- check unfolding regularP
   have hP :|M'|≤ d+m*k:=by rw [h0,abs_mul, abs_of_nonneg (inv_nonneg.mpr hc.le)]; refine (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=> H₀ i)) (inv_nonneg.mpr hc.le)).trans_eq ?_; rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ, inv_mul_cancel_left₀ hc.ne']
   let A:= R.activities.additive R.p
   have he i Z a:=additive_var R.p (stitch (G:=G) i Z a) R.activities h.labels
   have hz : |A U-A V|≤ m*life R.p δ:= tally hp.old A he (show 0≤life R.p δ from ?_)
   · have hi:R.exponent U-R.exponent V+ R.beta*(mainTerm R.clip R.path U'-mainTerm R.clip R.path V')=-(M'+(A U-A V)):= by unfold Rep.exponent A M'; ring
     rw [hi,abs_neg]; exact (abs_add_le ..).trans ((add_le_add hP hz).trans_eq (by unfold outset k d m; ring))
   unfold life; have hh : 0 ≤ δ:= budget_nonneg ((h.labels.boundE).choose_spec.2 0); have he:=meter_pos R.p.exponent_pos; positivity
end YM.MSbar.Heath
