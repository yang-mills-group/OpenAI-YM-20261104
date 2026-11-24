import YM.Frontier6.Exact.Dual

/-! Geometry through entire annuli (without price leakage to still finer sites).
Derivative interpolation and passing to any radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Function Filter Set Lattice Wilson RG Source Labels MergeProof MergeProof.Ribbons Next.UVStress
open Bid Spec Analysis Table Extraction.Lease Cells Extraction.Around OS Word MeasureTheory Org Canvas Platform
open Next.Extract Dash PhysicalNext.Repeat.Legato MergeProof.Acme
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order} {S:Table C.book}
variable (K:Final C F S){D d b N:ℕ}

lemma orbit_derives {n:ℕ} (w:S.Tag) (v:Fin n→ S.Tag)(y:Points n)(x:E4) (z:Axis) (a u:ℝ) (i:StateIndex K) (hx:Points.cons (chord z x a u) y∈conf (n+1)) (k:ℕ) :
   let X(s:S.Tag)(r:ℝ):=reading K i (chord z x a r) y v s.1 s.2
   let T:=trek K.sector.derivatives z w
   HasDerivAt (fun t:ℝ=> a^k • X (T k) t) (a^(k+1) • X (T (k+1)) u) u:= by
   intro X T
   let t:= T k; let V:= K.sector.derivatives; let R:= state K i; let v':=Fin.cons (α:=fun _:Fin (n+1)=> S.Tag) t v; let U:=Points.cons (chord z x a u) y;let G(x):= S.useAt R x v';
   have he : DifferentiableAt ℝ G U:= (((S.class_smooth R (hierarchy K i).smooth _) _ hx).contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp)
   have hg:HasDerivAt (fun p=> G (Points.cons (Ward.inc z x p) y)) (X (T (k+1)) u) (u*a):=by
      unfold X; rw [reads_at]; change HasDerivAt _ (S.useAt R U (Fin.cons ⟨_, V.deriv _ z t.snd⟩ v)) _; rw [(directional K i).kernels _ _ _ hx]; exact he.hasFDerivAt.comp_hasDerivAt (u*a) (Ward.forwards z x y _)
   have ht : HasDerivAt (fun v:ℝ=> v*a) a u:=by simpa using (hasDerivAt_id' u).mul_const a
   rw [pow_succ, ← smul_smul]; rw [show (fun z=> _ • X (T k) z)= ((a^k) • ((fun p=> G (Points.cons (Ward.inc _ _ p) y)) ∘ (fun v:ℝ=> v*a))) from ?_];exact (hg.scomp u ht).const_smul (a^k)
   ext1 t; unfold X; rw [reads_at]; rfl

lemma head_grade {n:ℕ} (w:S.Tag)(v:Fin n→ S.Tag) : totalGrade (Fin.cons w v)= w.1+2+totalGrade v:= by
   unfold totalGrade Clouds; rw [Fin.sum_univ_succ];rfl

variable {H:Table C.book}{M:ℕ→Table C.book}{Q:Bin H}{Y:DiffPlan S} (h:Base C F H M Q S Y) (hp:PairProducer C) (hg:G.Simple) (hW:Extraction.Wcmain C)(hG:Grill C F)
set_option quotPrecheck false
local notation "R"=> fuga C.path.levels
include hp hg
lemma slide_exits {r:ℝ}(hr:0 < r) : ∀ᶠ m:ℕ in atTop, ∀ (a:ℝ), R (m+1) ≤ a → a ≤ R m→ ∀ (x:E4), x ∈ arena a→ ∀ (n:ℕ) (y:Points n), clearC r y→ slide C.S (m+1) (Points.cons x (Points.cons 0 y)):=by
   have h': Tendsto (fun m=>4*(R m)) atTop (𝓝 0):=by simpa only [mul_zero] using! (((fugaPitch hp hg).thins (by norm_num)).const_mul (4:ℝ))
   have hX : Tendsto (fun i:ℕ=>4*C.S.a (i+1)) atTop (𝓝 0):=by simpa only [mul_zero] using! (C.S.shrinks.comp (tendsto_add_atTop_nat 1)).const_mul (4:ℝ)
   filter_upwards [h'.eventually (ge_mem_nhds (half_pos hr)),hX.eventually (ge_mem_nhds (half_pos hr))] with m hm hi a ha hb x hx n y hy
   have he: a/16< ‖x‖ ∧ ‖x‖<4*a:=hx; have ht: (1:ℝ) ≤ (C.path.levels.budget (m+1)).B:=by exact_mod_cast (C.path.levels.budget _).B_pos
   have hv: 4*C.S.a (m+1) ≤ a/16:=by unfold fuga at ha; linarith only [ha,mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=2) ht) (C.S.a_pos (m+1)).le,C.S.a_pos (m+1)]
   refine gap_append (gap_down hy (hi.trans (half_le_self hr.le))) x (fun i=> Fin.cases (by simpa [Points.cons] using hv.trans_lt he.1) (fun i=> ?_) i)
   have ht:r< ‖y i‖:=by simpa only [Points.cons, points_apply, Fin.cons_zero,Fin.cons_succ,sub_zero] using (show _ < ‖Points.cons 0 y i.succ - Points.cons 0 y 0‖ from hy _ _ (Fin.succ_ne_zero i).symm)
   have hq : ‖x‖ ≤ r/2:= le_trans (le_trans he.2.le (by linarith only [hb])) hm
   change _ < ‖y i-x‖; linarith only [hi,norm_sub_norm_le (y i) x,hq,ht]

variable (B:S.Field d)(P:S.Field b) {I:Type*}[Fintype I]{n:I→ℕ}(v:Tuple S n)
variable {j:ℕ→ℕ}{s:ℝ} (hs:1<s)(hj:Tendsto j atTop atTop)(hs':Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 s))
variable {r A:ℝ}(hr:0 < r)(ha:0 ≤ A)

include hG hs hj hs' hr ha
lemma contour_cost {F:ℕ→ℝ} {p:ℝ}(hF:Note C.S F p) : ∃ N:ℕ, ∀ᶠ i in atTop, ∀ (a:ℝ), R (i+1) ≤ a → a ≤ R i→ ∀ (y:Seen n),shapes r y→ ∀ (u:I → StateIndex K)(c:I→ℂ), (∀ k,‖c k‖ ≤ A) → ∀ z:Axis, ∀ x:E4,
   let V(t:ℝ):= chord z x (C.S.a (j i)) t
   (∀ t∈Icc (-arm N) (arm N), V t∈ arena a) →
    ∃ g:ℕ→ℝ→ℂ, g 0= listen K B P v y u c ∘ V ∧ (∀ k < N,∀ t∈Icc (-arm N) (arm N), HasDerivAt (g k) (g (k+1) t) t)∧ ∀ t∈Icc (-arm N) (arm N),‖g N t‖ ≤ F i:=by
    let T (z:Axis)(i:ℕ):= trek K.sector.derivatives z ⟨b,P⟩ i; let v' (i:I):= Fin.cons (α:=fun _:Fin (n i+1)=> S.Tag) (⟨d,B⟩:S.Tag) (v i)
    have hU(z:Axis)(i:ℕ): (T z i).1=b+i:= trek_h ..
    obtain ⟨k,hk⟩:= (eventually_all.mpr fun i:I=> (Tendsto.atTop_mul_const (sub_pos.mpr hs) (tendsto_natCast_atTop_atTop («R»:=ℝ))).eventually (eventually_gt_atTop ((totalGrade (v' i):ℝ)+b+2-p))).exists
    let Γ (i:I)(z:Axis):= Fin.cons (α:=fun _:Fin (n i+2)=> S.Tag) (T z k) (v' i)
    choose K' hw hK' using fun (i:I)(z:Axis) => tower_rough K (Γ i z) hG
    let C'(i:ℕ):= C.S.a (j i); let D(i:I)(z:Axis)(m:ℕ):= C' m^k*(K' i z (m+1));
    have he(i:I)(z:Axis): Note C.S (D i z) (-s*k+totalGrade (Γ i z)):= by
        exact (((Note.note_a C.S|>.relay j hj hs').powerN k|>.mills ((hw _ _).scales C.path.levels.fits.mesh)).swapP (by ring))
    let X:= (Fintype.card I:ℝ); let M:=(X+1)*(A+1); have hX:0 ≤ X:=by unfold X; positivity
    have hM:0 < M:=by unfold M; positivity
    have hp₀(i:I)(z:Axis):∀ᶠ m in atTop, D i z m ≤ F m / M:=by
        apply (he i z).outweigh (hF.splits (Note.notes C.S M hM)); unfold Γ; rw [head_grade,hU]; specialize hk i; push_cast; linarith only [hk]
    refine ⟨k,?_⟩
    filter_upwards [slide_exits (C:=C) hp hg hr,eventually_all.mpr fun i=> eventually_all.mpr (hp₀ i), eventually_all.mpr fun z=>eventually_all.mpr fun i=> (tendsto_add_atTop_nat 1).eventually (hK' i z)] with m hm hE hw a ht hl y hy u c hc z x
    intro V hv
    let g (i:ℕ)(n:I)(t:ℝ):ℂ:= C' m ^ i • reading K (u n) (V t) (Points.cons 0 (y n)) (v' n) (T z i).1 (T z i).2
    refine ⟨fun i t=>∑ n,c n * g i n t, ?_, ?_,?_⟩
    · ext1 t; unfold listen; simp only [g,pow_zero,one_smul]; rfl
    · intro i hi t h; exact HasDerivAt.fun_sum fun n hn=> (orbit_derives K ⟨b,P⟩ (v' n) (Points.cons 0 (y n)) x z (C' m) t (u n) (slide_conf C.S _ (hm a ht hl (V t) (hv t h) _ (y n) (hy n))) i).const_mul _
    intro t h; let w:=F m/M
    have hp'(i:I): ‖g k i t‖ ≤ w := by
       unfold g; rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos (j m)).le _), reads_at]
       refine le_trans (mul_le_mul_of_nonneg_left (hw z i (u i) _ (hm a ht hl (V t) (hv t h) _ _ (hy i))) (pow_nonneg (C.S.a_pos (j m)).le _)) (hE i z)
    apply (norm_sum_le ..).trans
    refine le_trans (Finset.sum_le_sum (g:=fun _:I=> A*w) (fun i _=> by rw [norm_mul]; exact mul_le_mul (hc i) (hp' i) (norm_nonneg _) ha)) ?_
    have hX':0≤ w:=div_nonneg (hF.pos _|>.le) hM.le; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc]
    exact (mul_le_mul_of_nonneg_right (show X*A ≤ M by unfold M; nlinarith only [hX,ha]) hX').trans_eq (mul_div_cancel₀ _ hM.ne')
end YM.Frontier6
