import YM.WilsonCoeffUV.Marked.Bounds.Reroll
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open scoped Topology BigOperators
variable {c f:Side}{ι α U V t:Type}{J K I S T:Finset ι}{D k:ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u A B C:ℝ}
variable [DecidableEq ι]
structure Wellness (k:ι→ℕ) (X:Outerm G D):Prop where
   quiet' : muting X
   level' : Solo k X
   filial : lazy X
variable {Y:Outerm G D} (H: Levels G)(L: ChartRatio G)
abbrev stout (m N:ℕ)(K k:ι→ℕ)(X: Outerm G D): Outerm G D:= unite (ll H m) K (fun p=> logO H L m N (X p) k)
abbrev margin (m N:ℕ)(K k:ι→ℕ)(X:Outerm G D): Outerm G D:= unite (ll H m) K (fun p=> edV H L m N (X p) k)
lemma Seating (X:Outerm G D)(p:G.Simple)(b:LocalRatio L)(t:m<N)(v:Wellness k X)(K:ι→ℕ): Wellness k (stout H L m N K k X):=by
    refine ⟨upQuiet _ _ _ (fun p=>logHush H L m N (X p) k), cone_L _ _ _ (fun k'=> step_L _ _ _ _ _ k t p b (v.level' k')), wield _ _ _ (fun i j S h=> log_g (fun S' a=> v.filial _ _ _ fun i e=> h i (a e)))⟩
theorem oneStep_log (X: Outerm G D)(p:G.Simple)(b:LocalRatio L)(t:m<N)(v:Wellness k X)(K:ι→ℕ)(q:ι→Cover):
    margin H L m N K k X q= levelsO (stout H L m N K k X q):=by
    funext S; let P:= stout H L m N K k X; let M p:= edV H L m N (X p) k; let Y p:= logO H L m N (X p) k
    have he:Solo k M:=fun i=> vol H L m N (X i) k t p b (v.level' i); have hf: Solo k Y:=fun i=> step_L H L m N (X i) k t p b (v.level' i)
    have hy:Wellness k P:= Seating H L X p b t v K; let Z:= margin H L m N K k X
    have ht:Solo k Z:= cone_L _ _ _ he; have h:lazy M:= fun i j S h=> levels_S_eq (fun s g=>v.filial i j _ (fun u x=> h u (g x))); have hu:lazy Y:=fun i j S h=> log_g (fun s g=> v.filial i j _ fun u x=>h u (g x))
    apply read_ext _ _ (ht q S) (placedO _ (hy.level' q) S); intro A n; have hw:= eCurse (K:=K) (ll H m) he hf h hu (fun i n s=>levels_log (M i) (he i) (edV_e H L m N (X i) k t p b) n s) A n q
    exact congr_fun (Equation.prod_u (feeble (Z q) A n) (feeble (P q) A n) _ hw (levels_exp _ (hy.level' q) (hy.quiet' q) A n)) S

omit H L [DecidableEq ι] in
lemma Wig.gait {f:Ten U (Cloth α) j}[NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup U][NormedSpace ℝ U]{p:ι→Cover}(g:U→L[ℝ]V)(v:Wig Bank.terrain p σ A S f):Wig Bank.terrain p σ (‖g‖*A) S (g ∘ f):= ⟨mul_nonneg (norm_nonneg _) v.1, fun y=> (g.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (v.2 y) (norm_nonneg _)).trans_eq (by ring))⟩
lemma crossBill (P:Patch)(K:ι→ℕ)(S:Finset ι): (Fintype.card (backRow P.L S):ℝ)* scalesK P K S=(P.L.val:ℝ)^mass K S:=by
   have he : Fintype.card (Site P.L)=P.L.val^4:=by rw [Fintype.card_pi]; simp
   let V:=(P.L.val:ℝ)
   unfold scalesK mass; rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_const,Fintype.card_fun,Fintype.card_coe,he]; push_cast; field_simp

section
variable [Fintype ι]{E U: Credit}{R:Realm G (e+1) E}
def shingled (p:ι→Cover)(S:Finset ι)(X: Outerm G D)(j:ℕ)(σ A:ℝ):Prop:=∀ i≤j,∀ r, Wig Bank.terrain p σ (A^S.card) S ((X p S).2 i r)
def AmpT (H G:Credit)(k:ι →ℕ) := H.prodC (G.powC (mass k Finset.univ))
def tollStep (G:Gauge)(D k K:ι→ℕ)(e:ℕ)(U E:Credit):= AmpT (vigor G D k e U E) E K
lemma furnish (p:Cloze D k R U)(X:Outerm G D)(h:Wellness k X)(g:R.anchor≤ m)(q:m<N)(v:ι→Cover)(K:ι→ℕ)(z:0≤A)(f:∀ t:backRow (ll R.draws m).L S,let x:=splitQ (ll R.draws m) v S t; safeB x (X x) S e (R.mint (m+1) (by omega)).σ A) : shingled v S (stout R.draws R.paid m N K k X) e (elixir (R.mint m g).gear) (R.cash (tollStep G D k K e U E) m*A):=by
    let T:= stout R.draws R.paid m N K k X; intro i t r; let P:=ll R.draws m; have hU := R.depth _ g; let C:=R.cash (vigor G D k e U E) m; let V:=R.cash E m; let K':=mass K Finset.univ; let E':=R.cash (tollStep G D k K e U E) m; have hE: E'=C*V^K':=by unfold E' cash tollStep AmpT; rw [Credit.products,Credit.power]
    by_cases hp:S=∅; · subst S; rw [(Seating R.draws R.paid X R.hG R.green q h K).quiet' v]; refine Wig.zero.more ?_; simp only [Finset.card_empty,pow_zero]; norm_num
    let s:= scalesK P K S; have hs:0≤s:= scalesBound ..; have hC:1≤ C:=Credit.purchase _ hU; have hV:1 ≤ V:=Credit.purchase _ hU
    let L w := logO R.draws R.paid m N (X w) k
    let Wt a :=portV P K L v S a; let η:= elixir (R.mint m g).gear; let γ:=C*A^S.card
    have ht a: Wig Bank.terrain v η (‖s‖*γ) S ((Wt a).2 i r):=by
        let Y:=splitQ P v S a; let Z:= inflate P S a; have hy:= waltz R p (X Y) (h.level' Y) (h.quiet' Y) m N g q v Z (f a) (le_refl S) z (r:=r) t; let U:= mend P Z D S; exact Wig.μ ((Wig.gait U hy).more (mul_le_of_le_one_left hy.1 (mend_norm ..))) s
    change Wig _ _ _ ( (E'*_)^S.card) S ((∑ i:backRow P.L S,Wt i).2 i r); rw [Prod.snd_sum,Finset.sum_apply,Finset.sum_apply]
    apply (Wig.sum (fun i _=> ht i)).more; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc,Real.norm_of_nonneg hs, show (Fintype.card (backRow P.L S):ℝ)*s=_ from crossBill P K S]; unfold γ; rw [←mul_assoc, mul_pow]
    refine mul_le_mul_of_nonneg_right (le_trans (b:=E') ?_ ?_) (pow_nonneg z _)
    · have hx : mass K S≤K':=by unfold K'; rw [stairK K (Finset.subset_univ _)]; exact Nat.le_add_right ..
      rw [hE,mul_comm]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC); exact (pow_le_pow_left₀ (by positivity) (R.taxes m g).height _).trans (pow_le_pow_right₀ hV hx)
    have hK:1≤ E':= Credit.purchase _ hU; nth_rw 1 [← pow_one E']; exact pow_le_pow_right₀ hK (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hp))
end
end YM.WilsonCoeffUV.Wheel.Mark
