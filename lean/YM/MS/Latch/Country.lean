import YM.MS.Latch.Sofa
/-!
# Costs for straight tadpole (unfolded full momentum) and bulk-oriented tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal
open scoped Topology ContDiff
variable {G:Gauge}{b c: Bool}{s t h:ℤ} {ι E F J:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F] {S:Scale ι}{n d:ℕ}{x y a b':ι→ℝ} {X Y:ι→ Law G} {K:ι→ Edge G}{w:Wire (BH G) E QP}
abbrev positive (S:Scale ι)(n:ℕ)(x y:ι→ℝ):= fun i=> S.length i^n*(x i*y i)
lemma plusLen (S:Scale ι) (t:ℤ)(k:ℕ)(a b c:ℝ)(i:ι): S.length i ^ ((k:ℤ)+t)*(a*b*c)=S.length i^t*( S.length i^k*(a*b*c)):= by rw [ zpow_add₀ (S.pos _).ne', zpow_natCast]; ring
abbrev nn (x:ι→ℝ): Prop:= ∀ i,0≤x i
lemma pos_nn (x:ι→ℝ)(h:nn x)(S:Scale ι){t:ℤ}: nn (fun i=>S.length i ^ t*x i):=fun _=>mul_nonneg (length_p ..) (h _)
lemma Cape.positive (h: Cape S X x w): nn x:= fun i=> nonneg_of_mul_nonneg_right (h.nonneg i 0 trivial ) (zpow_pos (S.pos _) _)
lemma np (S:Scale ι) (hx:nn x)(ha:nn a)(k:ℕ): nn (positive S k a x):= fun i=> mul_nonneg (pow_nonneg (S.pos _).le _) ( mul_nonneg (ha i) (hx i))
lemma joy (h:nn x)(ht:nn y): nn (x*y):= fun i=>mul_nonneg (h i) (ht i)
-- raw loop
lemma coalLoop (hx:Lease b true S X x)(he:Sheet S a K)(hc:Course b w) (i j:BH G): pole S (fun s q=> K s i j q.1 * X s ((i,q.1)::(j,-q.1)::sail w (q.2:E))) (fun s=> S.length s ^ pitch w* positive S 4 a x s) := by
    let A:= ContinuousLinearMap.fst ℝ QP E; let Q:= ContinuousLinearMap.snd ℝ QP E
    let v:Wire (BH G) (QP× E) QP:= (i,A)::(j,-A)::Wire.lift w Q; have hv :Course b v:= fun s=>by rw [show net v = A+(-A+ net w ∘L Q) from (by simp [v]) ]; rw [hc s]; simp -- notation CL
    convert! ( Rapid.mul ( he i j|>.rapid (F:=E) ) ( hx ( QP× E ) v hv ( fun q=> by simp [v]) ) ) using 1
    · ext; simp [Plane.Chart,v,A,Q]
    funext s; unfold positive pitch v; simp only [field_cons, field_lift]; let H:= S.length s; rw [show S.length s^4= S.length s^(4:ℤ) from rfl]
    calc
      _ = S.length s ^ ( (4:ℤ)+fieldDim wfield w) * (a s * x s):= by rw [zpow_add₀ (S.pos s).ne']; ring
      _ = _ := by rw [show (4:ℤ)+fieldDim wfield w= (4-wfield i-wfield j)+( wfield i+(wfield j+fieldDim wfield w)) by omega,zpow_add₀ ( S.pos s ).ne']; ring
lemma topCycle (hx:Lease b true S X x)(he:Sheet S a K)(hc:Course b w)(h1:nn x)(h2:nn a): pole S (fun s (q:QP × E)=> trc (K s) q.1 (X s) (sail w q.2)) (fun s=> S.length s^pitch w * positive S 4 a x s):= by
   simp_rw [at_trc]; refine allFin _ (fun i _=>allFin _ (fun j _=> coalLoop hx he hc i j) ?_) ?_ <;> exact pos_nn _ (np S h1 h2 _) S
where
 allFin {J:Type}{f:J→ι→ QP× E→ℂ}{a:ι→ℝ}(K: Finset J)(hF:∀ i∈ K,pole S (f i) a)(ht:nn a): pole S (fun i x=>∑ j ∈ K,f j i x) a:= fun b=> Costs.sum K (fun i hi=> hF i hi b) (fun i _ _=> div_nonneg (ht i) (pow_nonneg ( S.weight_pos ..|>.le) _)) -- universals J binder fixed ⇒ h type mismatch J
variable {μ:ι→Measure QP}
abbrev Mint (S:Scale ι)(μ:ι→Measure QP)(d:ℕ) := ∀ (E:Type)[ NormedAddCommGroup E ], S.full.Le (fun i (_:E)=>∫ q,S.dust d i q∂μ i) (fun i _=> fee S i)
lemma planC (hx:Lease b true S X x)(he:Sheet S a K)(hy: glob S μ d)(hk: Mint S μ d)(h1:nn x)(h2:nn a): Lease b false S (fun i=> cycle (K i) (μ i) (X i)) (a*x):= by
    intro E _ _ w hc hP; let F:= topCycle hx he hc h1 h2; unfold Cape; refine ?_; convert ( Rapid.consumes hy F ( Osc.sane F ) ( hk E )) using 1; rfl; ext s; change S.length _ ^ _ * (a s*x s)= _; unfold positive Snap.fee; field_simp [(S.pos s).ne']
lemma trunks (h:CourseK S a K)(hx:Lease true true S X x)(hy: Lease b true S Y y)(ha:nn a)(hL:nn x)(hR:nn y): Lease b false S (fun i=> tree parity ( K i ) (X i) (Y i)) ( positive S 4 a (x*y)) := by
   intro E _ _ w hv ht; unfold Cape Plane.Chart tree; simp_rw [sail_scatter,attaches,sail_degree,sail_net]; apply gather_bound w; intro l r hl;
   have hM: nn (fun i=> S.length i^pitch w* positive S 4 a (x*y) i):= pos_nn _ (np S ( joy hL hR) ha 4) S; refine Costs.sum _ (fun i _=> Costs.sum _ (fun j _=> Costs.add ?_ ?_) (fun i _ _=> hM i)) (fun i _ _=>hM i); all_goals
     have F (u:BH G)(z:ℂ) := (hx E ((u,-net l)::l) (fun _=>by simp) (fun _=>by simp)).L (ContinuousLinearMap.mul ℝ ℂ z)
     have H (u:BH G) := hy E ((u,net l)::r) ( attaches_course b _ _ _ hl hv u ) (fun _=>by simp)
   · convert! ((( Bound.linear ( -net l ) ( h i j ))).mul ( ( F i (cross (parity j) (degree (field parity) l)) ).mul ( H j ))) using 1; · simp only [neg_neg]; rfl
     funext k p; dsimp only [pitch,positive,Pi.mul_apply]; obtain hz:= (split_sum (wfield ∘ Prod.fst) hl); simp only [field_cons]; rw [show S.length k^4= S.length k^(4:ℤ) from rfl]; calc
           _ = S.length k^(fieldDim wfield w+(4:ℤ))*(a k *( x k*y k )):= by rw [ zpow_add₀ ( S.pos k ).ne']; ring
           _ = _ := by rw [show fieldDim wfield w+4=(4-wfield i-wfield j)+( wfield i+fieldDim wfield l)+(wfield j+fieldDim wfield r) from (by change fieldDim wfield l+fieldDim wfield r=fieldDim wfield w at hz; omega),zpow_add₀ (S.pos k).ne',zpow_add₀ (S.pos k).ne']; ring
   · convert! ((( Bound.linear ( net l ) ( h i j ))).mul ( ( F j (cross (parity i) ( parity j ^^ degree (field parity) l)) ).mul ( H i ))) using 1; · simp only [neg_neg]; rfl
     funext k p; dsimp only [pitch,positive,Pi.mul_apply]; obtain hz:= (split_sum (wfield ∘ Prod.fst) hl); simp only [field_cons]; rw [show S.length k^4= S.length k^(4:ℤ) from rfl]; calc
           _ = S.length k^(fieldDim wfield w+(4:ℤ))*(a k *( x k*y k )):= by rw [ zpow_add₀ ( S.pos k ).ne']; ring
           _ = _ := by rw [show fieldDim wfield w+4=(4-wfield i-wfield j)+( wfield j+fieldDim wfield l)+(wfield i+fieldDim wfield r) from (by change fieldDim wfield l+fieldDim wfield r=fieldDim wfield w at hz; omega),zpow_add₀ (S.pos k).ne',zpow_add₀ (S.pos k).ne']; ring
end YM.MS.Latch
