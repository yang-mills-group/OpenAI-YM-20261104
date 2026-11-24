import YM.RGComparison.Core16.Silk.Organza
/-!
# Location estimator. All budgets shared with coordinate-wise Profile `Witht` so usable at all
Θ-point words. Radius in Wires Fine Units, P Planner not buying growth thresholds implicitly. Contour
support algebra for polymer histories still elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Precision Finset
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D L U: Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D][Fintype L]
variable {X:Shelf G A D} {P:Planet X S ι k T} (p:Stuff G ι L) (ψ:(L→ G.Color)→ℝ) (R : Rail G ι→Roll)

-- Pole-free constituents
omit [Fintype ι] in
lemma tar {n:ℕ}(a:Wires G L n){c:ℝ}(hc:0≤c){Q:Finset ι}(hp:celery p Q c): |tagPrice p ψ a|≤ |warpPay ψ a| * (c+1)^n:= by
    unfold tagPrice; rw [abs_mul]; gcongr; unfold gauge; rw [abs_prod]; refine (prod_le_prod (g:=fun _=>c+1) (fun _ _=> abs_nonneg _) (fun i (_:i∈univ)=>?_)).trans (le_of_eq (by rw [prod_const,card_univ,Fintype.card_fin]))
    have he(i) : |clip p i| ≤ c+1:=by
       specialize hp i.1 -- hp mutated?
       unfold clip; rcases h:p i.1 with x|x <;> rw [h] at hp
       · simp [hc]
       exact (mono_cone ..).trans (le_trans (show ‖x‖ ≤ c from hp) (by linarith))
    exact he _

omit [Fintype ι] [Fintype L] in
lemma rails (p:Stuff G ι L){n:ℕ}(a:Wires G L n){Q:Finset ι}{c:ℝ}(hp:celery p Q c) (i:Wire G ι)(hi:i∈ weave p a): i.1∈Q:= by
    obtain ⟨j,_,he⟩:= List.mem_flatMap.mp hi; unfold field at he; rcases hh:p j.1 with x|x<;> rw [hh] at he
    · have ht:= hp j.1; rw [hh] at ht; rw [List.mem_singleton.mp he]; exact ht
    simp at he

variable {p R ψ}
omit [Fintype ι] in
lemma sight_cost {n i:ℕ}{x c:ℝ}(_hx:0≤x)(hc:0≤c){w:Rail G ι}{Q:Finset ι}(h: celery p Q c)
   (hp:∀ a:Wires G L n,|nth i (R (weave p a++w))| ≤ x) : |nth i (night p ψ R w n)|≤x*presence ψ c n:=by
   unfold night nth; rw [map_sum]; simp only [map_smul,smul_eq_mul]; unfold presence; rw [mul_sum]; refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=> (abs_mul ..).trans_le ((mul_le_mul (tar p ψ i hc h) (hp i) (abs_nonneg _) (by positivity)).trans_eq (mul_comm ..)))

variable (ψ)
def lint (b r:ℕ)(Q:ℝ) : ℝ:= ∑ i∈range (r+1), presence ψ Q (b+i)
lemma lint_nn (b r:ℕ){Q:ℝ}(he:0≤Q):0≤lint ψ b r Q:=sum_nonneg (fun i _=> by unfold presence; exact sum_nonneg fun k _=> by positivity)
variable {ψ}

-- n shift INCLUDED IN lemma bounds, +label arity b ∼ series after a Wick marker Laurent pole
lemma day_rate {V:ℕ→Roll} {F : ℕ→ℝ}{w r i:ℕ}(hF:∀ j≤r,0≤F j)(i':i≤r)(h:∀ n,w+n ≤ i→|nth (i-(w+n)) (V n)| ≤ F n): |nth i (day V w)| ≤ ∑ n∈range (r+1),F n:=by
   rw [Silk.vogue (t:=r) (show i≤_ by omega),nth,dawn,map_sum]; apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun j hj=> ?_))
   rw [shiftFront,PowerSeries.coeff_X_pow_mul']; split
   next h' => exact h _ h'
   rw [abs_zero]; exact hF _ (Nat.le_of_lt_succ (mem_range.mp hj))

omit [Fintype ι] in
lemma silk_price {j J n w:ℕ}{x c:ℝ}(hx:0≤x)(hc:0≤c){u:Rail G ι}{Q:Finset ι}(h:celery p Q c)(hJ:j≤J)
   (hp:∀ k, w+k ≤ j → ∀ a: Wires G L (n+k), |nth (j-(w+k)) (R (weave p a++u))| ≤ x) :
   |nth j (day (fun k=> night p ψ R u (n+k)) w)| ≤ x * lint ψ n J c:=by
    unfold lint; rw [mul_sum]; refine day_rate (fun i _ => mul_nonneg hx ?_) hJ (fun i hi=> sight_cost hx hc h (hp _ hi)); unfold presence; exact sum_nonneg fun i _=>by positivity

structure Lease (P:Planet X S ι k T)(u:ι→ℕ):Prop where
    lag (i j:ι): u i≤ u j+separation (P.loc i) (P.loc j)

def Local (C:ι→ℕ)(w:Rail G ι)(i:ℕ): Prop := ∀ j∈w,i≤ C j.1
omit [Fintype ι] in
lemma local_mono (C:ι→ℕ){i j:ℕ}{w:Rail G ι}(h:Local C w i)(hh:j ≤ i): Local C w j:= fun _ he=>hh.trans (h _ he)
variable {o:ι→ℕ}
omit [Fintype k] [Fintype T] [Fintype D] [Fintype A] [Fintype L] in
lemma local_stencil (B: Lease P o) (i:Wire G ι) {n j:ℕ}(a:Wires G L n) {u:Rail G ι}{p:Stuff G ι L}
    (h:celery p (P.heat i.1) X.Q)(hc:j+2*X.sector.b ≤ o i.1)(hu:Local o u j): Local o (weave p a ++u) j:= by
    intro k hk; rcases List.mem_append.mp hk with hj|hj; swap; exact hu k hj
    have ht : separation (P.loc i.1) (P.loc k.1) ≤ 2*X.sector.b:= (member ..).1 (rails p a h k hj); have h:=B.lag i.1 k.1; omega

-- hierarchy rough caps to propagate `cov?.typ` and general homogeneous bounds.


-- Cap grammar: next-rank taskBill (i,r) requires terms in earlier rank/length:
-- Wing summand bumped by j(w)+arity(a) where r=r-j; same rank only if j=0.
-- Easier index high rank first, then induction on d in Poll. want |·|≤ C times
-- input precision. Here x arbitrary receipt multiplier (possibly tiny).

structure Tagged (R:Rail G ι→ Roll)(j d N:ℕ)(o:ι→ℕ)(x:ℝ):Prop where
    full : ∀ u : Rail G ι, u.length≤ d → Local o u N→|nth j (R u)| ≤ x
    older : ∀ i<j, ∀ u : Rail G ι, u.length ≤ d+2+j → Local o u N → |nth i (R u)| ≤ x

def fringe (X : Shelf G A D)(j:ℕ):=∑ i:Option (G.ColorIndex×G.ColorIndex), lint (wing G i) 0 j X.Q
def stars (X : Shelf G A D)(j:ℕ) := ∑ i:A×(D→ Bool) × G.ColorIndex, lint (recipe X i) 2 j X.Q
def roar (X:Shelf G A D):= weights X.sector X.sector.b*(Planet.ferris X * X.Q)

def totalCap (X:Shelf G A D)(j d:ℕ):= d*fringe X j + roar X + weights X.sector X.sector.b* stars X j
lemma cap_pos (Y:Good X) (j d :ℕ):0≤totalCap X j d:=by have h:=Y.thick.1.le; unfold totalCap; have he:= (weights_pos X.sector X.sector.b).le; exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _=> lint_nn _ _ _ h)) (mul_nonneg he (mul_nonneg ferris_nn h))) (mul_nonneg he (sum_nonneg fun _ _=> lint_nn _ _ _ h))

variable (B:Lease P o)(H:P.Steady)(i:Wire G ι) {x:ℝ} {j d N:ℕ} {w:Rail G ι}(hx:0≤x)(hv:Local o w N)(hb:N+2*X.sector.b≤ o i.1)(hw:w.length ≤ d)(h:Tagged R j d N o x)
include H B hx hv hb hw h
-- Price rough; key recurrence shape. Uniform in period & footprint. Enrollment Prop h must be earned on paths below
lemma tasked : |nth j (taskBill P i R w)| ≤ totalCap X j d *x:=by
    have he(i : Fin w.length) : (w.eraseIdx i).length+1=w.length:= List.length_eraseIdx_add_one i.isLt
    have hk:= H.prices.thick.1.le; let F:=P.within i.1
    have hC : (F.card :ℝ) ≤ weights X.sector X.sector.b:= Nat.cast_le.mpr (price_cover (loc:=P.root) ((H.tickets 0 ⟨le_rfl,H.prices.thick.2.1.le⟩).edge) _ _)
    have ha:=sum_nonneg (f:=fun i:Option (G.ColorIndex× G.ColorIndex)=> lint (wing G i) 0 j X.Q) (s:=univ) fun _ _=> lint_nn _ _ _ hk; have hs:=sum_nonneg (f:=fun i:A×(D→Bool)×G.ColorIndex=> lint (recipe X i) 2 j X.Q) (s:=univ) fun _ _=>lint_nn _ _ _ hk
    have hu : ∀ a:Fin w.length, |nth j (wingK R (w.eraseIdx a) i w[a])| ≤ x * fringe X j:= by
       intro a; let f : Option (G.ColorIndex×G.ColorIndex):= scorecard i w[a]
       unfold wingK; have hp: celery (guide i) (P.heat i.1) X.Q:= fun _=> P.loc_heat _
       have hz := fun u=> @Nat.zero_add u
       apply le_trans ?_ (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun i:Option (G.ColorIndex×G.ColorIndex)=> lint (wing G i) 0 j X.Q) (fun i _=> lint_nn _ _ _ hk) (mem_univ f)) hx)
       rw [show night (guide i) _ R (w.eraseIdx a)= fun k=>night (guide i) (wing G f) R (w.eraseIdx a) (0+k) from funext fun _=> (by rw [hz])]; apply silk_price hx hk hp le_rfl
       intro k hk a'; let u:=weave (guide i) a'++w.eraseIdx a; have hl : Local o u N:= local_stencil B i a' hp hb (fun _ hj=>hv _ (List.eraseIdx_subset hj))
       have hh: List.length u ≤ k+w.length := by unfold u; rw [List.length_append]; have ht:=he a; have hm:= length_bound (guide i) a'; omega
       by_cases h₀:k=0
       · change |nth _ (R u)|≤_; rw [show j-(0+k)=j from by omega]; exact h.full _ (by omega) hl
       exact h.older _ (by omega) u (by omega) hl
    unfold taskBill; dsimp only [nth]; rw [map_sub,map_sub,map_smul,smul_eq_mul]; refine (abs_sub ..).trans ((add_le_add ((abs_sub ..).trans (add_le_add (show |nth j (windDown R i w)| ≤ d*(x*fringe X j) from ?_) ?_)) ?_).trans_eq (?_: d*(x*fringe X j)+roar X*x+(weights X.sector X.sector.b*(x*stars X j))=_))
    · unfold nth windDown; rw [map_sum]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>x*fringe X j) (fun i _=> hu i)).trans ?_); simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]; gcongr
    · rw [abs_mul]; exact mul_le_mul (offset_cost i H) (h.full _ hw hv) (abs_nonneg _) (mul_nonneg (weights_pos ..|>.le) (mul_nonneg ferris_nn hk))
    · unfold due; rw [map_sum]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=> x*stars X j) (fun a hA=> ?_)).trans ?_)
      swap; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hC (mul_nonneg hx hs)
      let v : A×(D→Bool) × G.ColorIndex:= (P.glyph a,P.hint a i.1,i.2); have hp: celery (path P i a) (P.heat i.1) X.Q:= preach H (a:=a) (i:=i) hA
      unfold cheaper
      apply le_trans ?_ (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun i:A×(D→Bool)×G.ColorIndex=> lint (recipe X i) 2 j X.Q) (fun i _=>lint_nn _ _ _ hk) (mem_univ v)) hx)
      apply silk_price hx hk hp le_rfl; intro k hk a'; have hl:= length_bound (path P i a) a'
      exact h.older _ (by omega) _ (by simp only [List.length_append]; omega) (local_stencil B i a' hp hb hv)
    unfold totalCap; ring

end YM.RGComparison.Core16.Silk
