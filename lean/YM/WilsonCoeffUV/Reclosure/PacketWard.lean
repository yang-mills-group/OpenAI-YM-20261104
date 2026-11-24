import YM.WilsonCoeffUV.Reclosure.Pricing
/-!
# The reexpression has its OWN tensors and Ward, through higher orders
Each nonzero-rank packet `g^(grade-slots) uncut(A)` standalone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary AnalyticNext.QuarticMatch.Estimate Near PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{s a:ℝ}
variable {A:ℕ→Atom G t}

abbrev fire (A:ℕ→Atom G t) (k:ℕ): Gen ℝ (YForest G):= shine (spreadW A (t+k))
abbrev written (A:ℕ→Atom G t)(n:Side): PChart G n:=sprig (seriesScore n A) t
lemma paid_packet (h:0<s)(hw: SumBudget (fun i=>(A i).budget s) a)(hp:0<t)(k i:ℕ): Yields (fun n=>written A n k i) (fire A k i):=by
    by_cases H:t+k=i; swap; · simp_rw [written,sprig,fire,shine_dark H]; exact Yields.zero
    subst i; obtain ⟨t,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : t≠0)
    -- A bound sum across shift now +1 invol
    simp_rw [written,sprig,fire,shine_lit]; rw [show t.succ+k=t+k+1 by omega]; exact sponsored h hw _
lemma mantle_input (A:Link G c):input G c A=mantle (G:=G) (c:=c) A:=by ext1 i; rw [bare_linkC]; unfold input; rw [Work.F03.represent_link]; apply congr_arg; ext p; rw [arm_apply]; rfl
lemma parchment (h:0<s)(hw: SumBudget (fun i=>(A i).budget s) a)(hg:∀ i,(A i).Invariant)(c:Side): rollTest (flash (written A c)) (flash (written A c)) 1 0 := by
    let F:=seriesScore c A
    have he:= score_analytic c A h hw
    have hb: Green F:=he.contDiffAt
    have hx:= ink_low c A h hw
    have hh: X^t * flash (sprig F t)=jet F:= by
         apply moves F; intro i hi; rw [jet_apply]; rw [show rye F i=0 from funext (fun u=>by unfold rye; rw [(rays_jet he t).1 hx i hi]; simp),map_zero]
    intro Y hY q X X' u
    have hu :∀ᶠ w:Lawn Y in 𝓝 0, F (X w)=F (X' w):=by
       filter_upwards [u.shift] with w h
       unfold F seriesScore; simp_rw [mantle_input]; rw [h,Lattice.pull_id,Work.F05.uncut_gauge A hg]
    apply mul_left_cancel₀ (a:=(PowerSeries.X:Blue.Ink Y)^t) (pow_ne_zero t X_ne_zero)
    change _* train (Blue.spool X) (flash (sprig F t))= _ * train (Blue.spool X') (flash (sprig F t))
    conv_lhs=>arg 1; arg 1; rw [← train_X (Blue.spool X)]
    conv_rhs=>arg 1; arg 1; rw [← train_X (Blue.spool X')]
    rw [← map_pow, ← map_pow,← map_mul, ← map_mul,hh,traveling _ u.g₀ u.f₀ _ hb,traveling _ u.g₁ u.f₁ _ hb]; exact jet_congr hu
-- upgrade vertical without signed lights (aggregate W remains fully signed).

lemma riseV (P: Crude G)(V:Canvas G)(hf:∀ i j,Yields (fun n=>P n i j) (V i j))(h:∀ n,rollTest (flash (P n)) (flash (P n)) 1 0)(hp:∀ n i,Pure (P n i))(ht:∀ n,shellK t (P n)) (k): pillar V k:= by
   intro b x
   let R (n:Side): Gen ℝ (Co n (Hooks G)) := ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k, (lamp b 0 (wrap n x,v) j z.1 (P n z.2)+lamp 0 b (wrap n (x-step v),v) j z.1 (P n z.2))
   have he : ∀ᶠ n in atTop,R n=0:= by
    filter_upwards [eventually_ge_atTop (⟨2,by decide⟩:Side)] with n hn
    simp_rw [R, map_sub,wrap_step]; exact one_site (h n) _ (ht n) (hp n) hn ..
   ext1 l; ext1 w; refine tendsto_nhds_unique (f:=fun n=> R n l (foldUnder n ∘ w)) (l:=atTop) ?_ (tendsto_const_nhds.congr' (he.mono (fun n hn=> by change 0 = R n l _; rw [hn]; rfl)))
   simp_rw [R,Finset.sum_apply,Pi.add_apply]; apply tendsto_finsetSum; intro i _; apply tendsto_finsetSum; intro j _; apply tendsto_finsetSum; intro v hv
   exact (lamp_tend b 0 (x,i) j _ (P:=fun n=>P n v.2) (hf v.2) _ w).add (lamp_tend 0 b (x-step i,i) j _ (P:=fun n=>P n v.2) (hf v.2) _ w)
-- bundle shift prior

def chess (A:ℕ→Atom G t)(m k:ℕ) : Gen ℝ (YForest G):= if m≤k then fire A (k-m) else 0
lemma postponed (h:0<s)(hw: SumBudget (fun i=>(A i).budget s) a)(hp:0<t)(hv:∀ i,(A i).Invariant)(k): vertical (chess A k):= by
    let R:= written A
    let Q m (n:Side): PChart G n:= fun i=> if m ≤ i then R n (i-m) else 0
    have hz n i: Pure (R n i):=sprig_pure _ (score_analytic n A h hw).contDiffAt _ _
    have he m n i: Pure (Q m n i):= by unfold Q; split; apply hz; exact Pure.zero
    have hp m n:shellK t (Q m n):=by
       intro i j hi; unfold Q; split; · exact sprig_count _ _ _ _ (by omega)
       rfl
    have hu n:rollTest (flash (R n)) (flash (R n)) 1 0:=parchment h hw hv n
    have hM n: flash (Q k n)=PowerSeries.X^k*flash (R n):=by
       apply PowerSeries.ext; intro i; rw [coeff_X_pow_mul']; unfold Blue.flash; simp only [coeff_mk]
       unfold Q; split
       · rfl
       simp [totalR]
    have hW n: rollTest (flash (Q k n)) (flash (Q k n)) 1 0:=by
       rw [hM]; intro V _ q X X' H; rw [map_mul,map_pow,train_X,map_mul,map_pow,train_X,hu n H]
    have hE i j: Yields (fun n=>Q k n i j) (chess A k i j):=by
       simp only [Q,chess]; split; · exact paid_packet h hw (by assumption) ..
       exact Yields.zero
    exact fun b x m=> riseV _ _ hE hW (he k) (hp k) m b x

lemma dressing (h:0<s)(hw: SumBudget (fun i=>(A i).budget s) a)(hp:0<t)(hv:∀ i,(A i).Invariant)(k r) : Bank.mural (fire A k r):= mural_sigma (written A) (fire A) (parchment h hw hv) (fun _=>sprig_count _ _) (fun n _=>sprig_pure _ (score_analytic n A h hw).contDiffAt _ _) k r (paid_packet h hw hp ..)
lemma proven (h:0<s)(hw: SumBudget (fun i=>(A i).budget s) a)(hp:0<t)(k r): Blue.Smooth (fire A k r):= (paid_packet h hw hp k r).sym (Eventually.of_forall fun n=> (sprig_pure (seriesScore n A) (score_analytic n A h hw).contDiffAt t k r))
lemma cap_pay (h:0<s)(hw: SumBudget (fun i=>(A i).budget s) a)(hp:0<t)(k r): Amber terrain (steep s) (a*garden G s t r) (fire A k r):=by
    by_cases H:t+k=r; swap; · rw [fire,shine_dark H]; exact Amber.zero.le (mul_nonneg (cap_nn hw) (garden_nn G h t r))
    subst r; rw [fire,shine_lit]
    obtain ⟨b,p⟩:= Nat.exists_eq_succ_of_ne_zero (by omega:t+k≠0); rw [p]; exact coronation h hw b
end YM.WilsonCoeffUV.Bank.Mosaic
