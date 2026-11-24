import YM.Next.FREE_KERNELS.Traffic
import YM.XSpace.Treasure

/-!
# Use the actual Green functions of Satin/Wander/Sail on both configurations

Expose stencil ℓ1/∞² costs for the periodic image prescription and its strict bulk
counterpart. No subsequence or ξ cut. Norm estimates at raw stencil step price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Outline
open Function Lattice RG Wilson Source Source.Drops Next.Rank.Normal Contraction Chart2 Finsupp JetGauge Legs MvPolynomial Feynman Filter Further.FreeCovariance.KP
open Sail (reach gd cover)
open scoped Topology BigOperators
variable {G:Gauge} {R:Period} {n:Side} {Q: Type*}[AddCommGroup Q][One Q]

def coal (f:Four Q→ℝ) (p q:Bone G Q):ℂ:= if p.1.2=q.1.2∧p.2=q.2 then ↑(f (q.1.1-p.1.1)) else 0

def duskCov (G:Gauge): JetGauge.Cov (Bone G ℤ):=⟨coal cover,fun i j=>by
  dsimp only [coal]; split_ifs with h hh hh
  · obtain ⟨r,R⟩:= h; rw [← neg_sub i.1.1 j.1.1]; apply congr_arg; have he (g: Cover): cover (-g)=cover g := by
      have hx:= Sail.toward [] Top.side Top.grows g; have hh:= Sail.toward [] Top.side Top.grows (-g); have p(n:Side): Sail.seen [] n (-g)= Sail.seen [] n g:=by rw [Sail.seen_bare,Sail.seen_bare,map_neg,Potential.even]
      exact congr_arg Complex.re (tendsto_nhds_unique (hh.congr fun i=> p (Top.side i)) hx)
    apply he
  · exact False.elim (hh ⟨h.1.symm,h.2.symm⟩)
  · exact False.elim (h ⟨hh.1.symm,hh.2.symm⟩)
  · rfl
  ⟩

def dusk (G:Gauge):Given G ℤ:=⟨Chart.lug 0,by simp [Chart.lug], duskCov G,fun k x y=> k≤ reach (x-y)⟩
def dawn (G:Gauge) (R:Period): Given G (Per R.side):= ⟨Chart.wreath _,by simp [Chart.wreath],wide (meet G R),fun k x y=> k≤ separation x y∧ k ≤ separation x (-y)⟩
def mirror (u:Roller R G): Roller R G:=(R.reflect u.1,u.2)
lemma mixed_coal (p q: Roller R G) : coal (gd R.side) p q= ↑(mixed p.1 q.1 p.2 q.2):=by
  unfold mixed coal; split_ifs with h h' h'; exact congr_arg (fun x:ℝ=>(x:ℂ)) (green_pair q.1.1 p.1.1); tauto; tauto; simp
lemma paired (p q:Roller R G): (dawn G R).grant.cov p q= coal (gd R.side) p q- coal (gd R.side) (mirror p) q:=by unfold dawn; rw [mixed_coal (R:=R),mixed_coal (R:=R), ← Complex.ofReal_sub]; exact Feynman.green_entries (R:=R) ..

def oneBeat (f:Four Q→ℝ) (c:PlaqAxes) (d:Axis) (i j:G.ColorIndex)(x:Four Q):ℂ:= if i=j then if d=c.val.1 then -↑(Sail.Δf c.val.2 f x) else if d=c.val.2 then ↑(Sail.Δf c.val.1 f x) else 0 else 0
lemma paid (f:Four Q→ℝ) (p:Wing G Q)(q:Bone G Q): linearCombination ℂ (coal f q) (ringBell p)= oneBeat f p.1.2 q.1.2 q.2 p.2 (p.1.1-q.1.1):=by
  let d:=q.1.2; let c:=p.1.2; have he : c.val.1≠c.val.2:=c.property.ne
  unfold ringBell; simp only [map_sub,map_add,linearCombination_single,one_smul,coal]
  unfold oneBeat; split_ifs <;> simp_all [c, Sail.Δf,sub_add_eq_add_sub]
lemma evening (p:Wing G ℤ)(q:Bone G ℤ)(x y:Cover): (dusk G).reacts p q x y=oneBeat cover p.1.2 q.1.2 q.2 p.2 (p.1.1+x-(q.1.1+y)):=by
  apply (paid cover ((dusk G).front x p) ((dusk G).burn y q)).trans _; unfold Given.front dusk Chart.lug Given.burn Given.points Chart.shift Chart.atop Chart.roll Chart.move; simp; rfl
lemma morning (p:Wing G ℤ)(q:Bone G ℤ)(x y:R.Sites): (dawn G R).reacts p q x y = oneBeat (gd R.side) p.1.2 q.1.2 q.2 p.2 (wrap R.side p.1.1+x-(wrap R.side q.1.1+y)) -
    oneBeat (gd R.side) p.1.2 q.1.2 q.2 p.2 (wrap R.side p.1.1 + x - (- (wrap R.side q.1.1+y)-step q.1.2)):=by
  let g:=dawn G R; let v:=g.front x p; let e:=g.burn y q
  change linearCombination ℂ (g.grant.cov e) _ = _
  rw [show g.grant.cov e = coal (gd R.side) e - coal (gd R.side) (mirror e) from funext fun i=> paired e i,show ∀ a b : Bone G (Per R.side)→ℂ,∀ (x: Bone G (Per R.side)→₀ℂ), (linearCombination ℂ (a-b)) x= (linearCombination ℂ a) x-(linearCombination ℂ b) x by intro a b x; simp [linearCombination_apply,Finsupp.sum,mul_sub,Finset.sum_sub_distrib],paid,paid]; rfl
lemma saving_fee {r B k:ℕ}(h:r≤k+B): saving k ≤ (1+(B:ℝ))*saving r:=by
  unfold saving; have hh:(r:ℝ)≤(k:ℝ)+B:= by exact_mod_cast h
  have h0 : 0≤ (k:ℝ)*B:= by positivity
  field_simp; nlinarith
lemma size_fee (y:Site n): pdist y ≤ n.val:=by obtain ⟨i,hi⟩:= Sail.reached (lift y); have he:= lift_centers y i; rw [← Sail.reaches, ← hi]; omega
lemma pc_cast (n:Side)(p:Cover): pdist (wrap n p) ≤ reach p:= Finset.sup_le fun i _=> (Next.Free.below_wrap n p i).trans (Sail.reach_at p i)
lemma horizon (a b:Cover)(p:Site n)(k:ℕ)(hh:k≤pdist p): saving (pdist (p+wrap n (a-b))) ≤ (1+(reach (a-b):ℝ))*saving k:=by
  apply saving_fee; calc
    _ ≤ pdist (p + wrap n (a-b) + -wrap n (a-b)):= by rw [add_neg_cancel_right]; exact hh
    _ ≤ _ := by apply (pdist_triangle ..).trans; rw [pdist_neg]; gcongr; apply pc_cast
lemma cut_strength (v:Axis): ∃ C:ℝ,0<C∧∀ x:Cover, |Sail.Δf v cover x|≤ C*saving (reach x):=by
  obtain ⟨C,hC,H⟩:= Sail.covers_decays [v]; refine ⟨C,hC,fun x=>(H x).trans (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
  exact (Sail.carry_weight (Sail.reach x) (show 1≤(2+[v].length) by simp)).trans_eq (pow_one _)
lemma horizon_cost (v:Axis): ∃ C:ℝ,0<C∧∀ n:Side,∀ x:Site n,|Sail.Δf v (gd n) x|≤C*saving (pdist x):=by
  obtain ⟨C,hC,H⟩:= Sail.seam [v]; refine ⟨C*3,by positivity,fun n x=>(H n x).trans ?_⟩; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hC.le
  have ht:(n.val:ℝ)⁻¹ ≤ 2*saving (pdist x) := by
    have he : (pdist x:ℝ)≤n.val:= by exact_mod_cast size_fee x
    have hp : 1≤(n.val:ℝ):=by exact_mod_cast n.pos
    unfold saving; field_simp; linarith
  have hp : Sail.carry (2+[v].length) (pdist x)≤ saving (pdist x):=(Sail.carry_weight (pdist x) (show 1≤(2+[v].length) by simp)).trans_eq (pow_one _)
  linarith

lemma fee_d (c:PlaqAxes) (d:Axis) (i j:G.ColorIndex): ∃ C:ℝ, 0<C ∧ ∀ x:Cover, ‖oneBeat cover c d i j x‖≤ C*saving (reach x):=by
  by_cases he:i=j <;> by_cases H:d=c.val.1 <;> by_cases hx:d=c.val.2 <;> simp only [oneBeat] <;> (first | simp only [if_pos he] | simp only [if_neg he]) <;> (try first | simp only [if_pos H] | simp only [if_neg H]) <;> (try first | simp only [if_pos hx] | simp only [if_neg hx]) <;> simp only [norm_neg,norm_zero,Complex.norm_real,Real.norm_eq_abs] <;> first | exact cut_strength _ | exact ⟨1,zero_lt_one,fun x=> by rw [one_mul]; exact (saving_ok ..).le⟩
lemma fee_g (c:PlaqAxes) (d:Axis) (i j:G.ColorIndex): ∃ C:ℝ, 0<C ∧ ∀ n:Side,∀ x:Site n, ‖oneBeat (gd n) c d i j x‖≤ C*saving (pdist x):=by
  by_cases he:i=j <;> by_cases H:d=c.val.1 <;> by_cases hx:d=c.val.2 <;> simp only [oneBeat] <;> (first | simp only [if_pos he] | simp only [if_neg he]) <;> (try first | simp only [if_pos H] | simp only [if_neg H]) <;> (try first | simp only [if_pos hx] | simp only [if_neg hx]) <;> simp only [norm_neg,norm_zero,Complex.norm_real,Real.norm_eq_abs] <;> first | exact horizon_cost _ | exact ⟨1,zero_lt_one,fun n x=> by rw [one_mul]; exact (saving_ok ..).le⟩
lemma slope_circle (c:PlaqAxes) (d:Axis) (i j:G.ColorIndex) : Summable fun x:Cover=> ‖oneBeat cover c d i j x‖^2:=by
  by_cases he:i=j; simp only [oneBeat,if_pos he]
  · by_cases hx:d=c.val.1
    · simp only [if_pos hx,norm_neg,Complex.norm_real,Real.norm_eq_abs,sq_abs]; exact Sail.ℓ2_cover c.val.2
    by_cases H:d=c.val.2
    · simp only [if_neg hx,if_pos H,Complex.norm_real,Real.norm_eq_abs,sq_abs]; exact Sail.ℓ2_cover c.val.1
    simp only [if_neg hx,if_neg H]; simp
  simp [oneBeat,he]
lemma slope_case (c:PlaqAxes) (d:Axis) (i j:G.ColorIndex) : ∃ C:ℝ,0<C∧∀ n:Side, (∑ x:Site n, ‖oneBeat (gd n) c d i j x‖^2) ≤ C:=by
  obtain ⟨C,hC,H⟩:= Sail.ℓ2_period; refine ⟨C,hC,fun n=>?_⟩
  by_cases he:i=j <;> by_cases ht:d=c.val.1 <;> by_cases hx:d=c.val.2 <;> simp only [oneBeat] <;> (first | simp only [if_pos he] | simp only [if_neg he]) <;> (try first | simp only [if_pos ht] | simp only [if_neg ht]) <;> (try first | simp only [if_pos hx] | simp only [if_neg hx]) <;> simp only [norm_neg,norm_zero,Complex.norm_real,Real.norm_eq_abs,sq_abs] <;> first | exact H .. | simpa using hC.le
private lemma artificial (a b x y:Cover)(k:ℕ)(h:k ≤ reach (x-y)): saving (reach (a+x-(b+y))) ≤ (1+(reach (b-a):ℝ))*saving k:=by
  apply saving_fee; exact h.trans ((by rw [show x-y=(a+x-(b+y))+(b-a) by abel]; -- rewrites all
                                       exact Sail.tree ..))
theorem night (G:Gauge): Society (R:=fun _ : Unit=>ℤ) (fun _=> dusk G):=by
  refine ⟨?_,?_,?_,fun i p q h=>?_⟩
  · obtain ⟨C,hC,H⟩:= Sail.covers_decays []; refine ⟨C,hC,fun i j k=>?_⟩; change ‖coal cover j k‖≤C; unfold coal; split; rw [Complex.norm_real,Real.norm_eq_abs]; apply (H _).trans; apply mul_le_of_le_one_right hC.le (Sail.carry_at ..); simpa using hC.le
  · intro a b; obtain ⟨C,hC,H⟩:=fee_d a.1.2 b.1.2 b.2 a.2; let c:=reach (b.1.1-a.1.1); refine ⟨C*(1+c),by positivity,fun i x y n h=> (by rw [evening]; apply (H _).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left (artificial _ _ x y n h) hC.le)⟩
  · intro a b; obtain hh:=slope_circle a.1.2 b.1.2 b.2 a.2; let f:=fun x:Cover=> ‖oneBeat cover a.1.2 b.1.2 b.2 a.2 x‖^2; set C:= ∑' x:Cover,f x; have hC : 0≤ C:= tsum_nonneg fun _=> sq_nonneg _
    refine ⟨C+1,by positivity,fun _ x s=> ?_⟩; simp_rw [evening]; set g:=fun y:Cover=> a.1.1+x-(b.1.1+y); have ht:Injective g:= by unfold g; intro i j h; rwa [sub_right_inj,add_right_inj] at h
    apply le_trans _ (le_add_of_nonneg_right zero_le_one); change ∑ x∈s, f (g x) ≤ _; rw [← Finset.sum_image (g:=g) (f:=f)]; apply Summable.sum_le_tsum _ (fun x _=> sq_nonneg _) hh; exact fun i _ j _ h=> ht h
  change coal _ p q=0; rw [coal, if_neg]; tauto

theorem dawning (G:Gauge): Society (R:=fun R:Period=>Per R.side) (fun R=> dawn G R):=by
  refine ⟨?_,?_,?_,fun i p q h=>?_⟩
  · obtain ⟨C,hC,H⟩:= Sail.general_period_bound; have hp(n:Side)(p q:Bone G (Per n)): ‖coal (gd n) p q‖≤C:=by unfold coal; split; rw [Complex.norm_real, Real.norm_eq_abs]; apply H; simpa using hC.le
    exact ⟨C+C,by positivity,fun i p q=> by rw [paired (R:=i)]; exact (norm_sub_le ..).trans (add_le_add (hp ..) (hp ..))⟩
  · intro a b; obtain ⟨C,hC,H⟩:=fee_g a.1.2 b.1.2 b.2 a.2
    let c:= a.1.1-b.1.1; let d:= a.1.1+b.1.1+step b.1.2
    set F:=(1+(reach c:ℝ)); set G':=(1+(reach d:ℝ)); refine ⟨C*F+C*G',by dsimp [F,G']; positivity,fun R x y k hk=>?_⟩
    let A:=x-y+wrap R.side c; let B:= x - (-y)+wrap R.side d
    rw [morning]; have hc : wrap R.side a.1.1+x-(wrap R.side b.1.1+y)=A := by unfold A c; rw [map_sub]; abel
    rw [hc,show wrap R.side a.1.1+x-(-(wrap R.side b.1.1 +y)-step b.1.2)=B from by unfold B d; rw [map_add,map_add,wrap_step]; abel]; apply (norm_sub_le ..).trans; rw [_root_.add_mul]; apply (add_le_add (H R.side A) (H R.side B)).trans; rw [mul_assoc,mul_assoc]; apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ hC.le; simpa using horizon c 0 (x-y) k hk.1
    apply mul_le_mul_of_nonneg_left _ hC.le; simpa only [B,G',sub_zero] using horizon d 0 (x - -y) k hk.2
  · intro a b; obtain ⟨C,hC,H⟩:= slope_case a.1.2 b.1.2 b.2 a.2; refine ⟨4*C,by positivity,fun R x s=>?_⟩; simp_rw [morning]; let g:= oneBeat (gd R.side) a.1.2 b.1.2 b.2 a.2; let z:= wrap R.side a.1.1+x; let w:= wrap R.side b.1.1; let F (y : R.Sites):= z-(w+y); let T (y : R.Sites):=z- (- (w+y)- step b.1.2)
    have ht (p:R.Sites→R.Sites) (he:Injective p): ∑ i∈s, ‖g (p i)‖^2 ≤ C:=by rw [← Finset.sum_image (g:=p) (f:=fun i=> ‖g i‖^2)]; apply le_trans _ (H R.side); exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=> sq_nonneg _); exact fun i _ j _ h=> he h
    calc _ ≤ ∑ y∈s,(2*‖g (F y)‖^2+2*‖g (T y)‖^2):=Finset.sum_le_sum (fun i _=> by apply le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (g (F i)) (g (T i))) 2); nlinarith [sq_nonneg (‖g (F i)‖ - ‖g (T i)‖)])
         _ ≤ 4*C:= by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]; have hh:=ht F (fun i j h=> by simpa [F] using h); have ho:= ht T (fun i j h=> by simpa [T] using h); linarith
  rw [paired]; unfold coal; change (if _∧p.2=q.2 then _ else _)-(if _∧p.2=q.2 then _ else _)=_; simp [h]
end YM.XSpace.Outline
