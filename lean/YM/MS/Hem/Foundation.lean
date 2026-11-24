import YangMills.WilsonProof.NativeSupport.YM.MS.Hem.Choose
/-!
# All homogeneous Taylor ambiguity resolved: ℓ=0 by bare coefficient,
 ℓ>0 by non-resonance.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W S: Mob G} {x:ℂ} {b:Bool} {r k:ℤ} {n m ℓ:ℕ}
-- point neighborhood & independent value
lemma Will.preC (P:LeanC G)(h:Need P)(hp:W ∈ P)(ht:kPrice W)(j:ℕ)(x:ℂ): cPos j x W∈P:= P.sum_mem fun i _=> P.smul_mem _ (h.jet hp ht i)
lemma Will.preR (P:LeanR G)(h:Will P)(hp:W ∈ P)(ht:kPrice W)(j:ℕ)(hx:star x=x): cPos j x W∈ P:= by
    refine P.sum_mem (t:=Finset.range j) (f:=fun r:ℕ=>(x+r)⁻¹ • Tad W r) fun i hi=> ?_; obtain ⟨u,rfl⟩:= Complex.conj_eq_iff_real.mp hx; convert P.smul_mem ( (u + (i:ℝ))⁻¹) (h.jet hp ht i) using 1; ext; simp [Complex.real_smul]
lemma road (P:LeanC G)(h:Need P)(hp:W∈P)(ht:kPrice W)(hx:0<(vamp x n ℓ).re+(n+1:ℕ)): Bless n ℓ x W∈ P:= by unfold Bless; split; simp only [add_zero]; exact h.lamp hp ht hx; exact P.add_mem (h.lamp hp ht hx) (Will.preC P h hp ht ..) -- syntax
lemma seen (P:LeanR G)(h:Will P)(hp:W∈P)(ht:kPrice W)(hb:star x=x)(hx:0<(vamp x n ℓ).re+(n+1:ℕ)): Bless n ℓ x W ∈ P:= by
    have he:star (vamp x n ℓ)= vamp x n ℓ:= by simp [vamp,toll,hb]
    unfold Bless; split; simpa only [add_zero] using h.light hp he ht hx; exact P.add_mem (h.light hp he ht hx) (h.preR P hp ht _ he) -- order
lemma modular (hp:kPrice W)(hx:∀ i<n, x+i≠0): Trail (cPos n x W) (haze n W) x:= by
    induction n with
    | zero=> simp only [cPos,haze,Finset.range_zero,Finset.sum_empty]; exact Trail.zero
    | succ n ih=>
       unfold cPos haze; rw [Finset.sum_range_succ,Finset.sum_range_succ]; refine Trail.plus (ih fun i hi=> hx i (by omega)) ?_; simpa only [inv_smul_smul₀ (hx n (lt_add_one n))] using Trail.smul (Trail.u_pose (x:=x) hp (n:=n)) ((x+(n:ℂ))⁻¹)
lemma GaugeTrail (hp:kPrice W)(hx:0<x.re+(n+1:ℕ))(hv:∀ i<n+1,x+i≠0) : Trail (progress (n+1) x W+cPos (n+1) x W) W x:= by
    have he := Trail.plus (Trail.prog_p hp hx) (modular hp hv); rwa [Hem.clear,sub_add_cancel] at he
lemma yellow (h:kPrice W)(hp:0<ℓ): ∀ᶠ i in dotty,Trail (Bless n ℓ i W) W (vamp i n ℓ):= by filter_upwards [vamp_up n ℓ,vamp_room n ℓ hp] with i hi hC; exact (by simp only [Bless, ↓reduceIte, hp.ne']; exact GaugeTrail h hi hC)
lemma pale (h:kPrice W)(he:Wind (fun t=>plow (-(n:ℂ)) t W) atBot 0) : Trail ( Bless n 0 x W) W (vamp x n 0) ∧ Wind (fun t=>plow (-(n:ℂ)) t ( Bless n 0 x W)) atBot 0:= by
    refine ⟨?_,?_⟩; · obtain hp: Trail (progress (n+1) (vamp x n 0) W) (Hem.clear (n+1) W) (vamp x n 0):= Trail.prog_p h (by simp); simpa only [Bless,↓reduceIte,add_zero,peer h he] using hp
    simp only [Bless,vampV,add_zero,if_true]; exact frame_lim
-- unify quantification eventually all W with T1; h momentum? user needs to prove all n fixed z body. Later Pose pull.
lemma blessAll (f:ℂ→Mob G)(h:mer f)(he:ℓ=0→ ∀ᶠ i in dotty, Wind (fun t=>plow (-(n:ℂ)) t (f i)) atBot 0): ∀ᶠ i in dotty, Trail ( Bless n ℓ i (f i)) (f i) (vamp i n ℓ)∧(ℓ=0→ Wind (fun t=>plow (vamp i n ℓ) t ( Bless n ℓ i (f i))) atBot 0):= by
    by_cases hr:ℓ=0
    · subst ℓ; filter_upwards [he rfl,h.price] with i hi hp; exact ⟨(pale hp hi).1,fun _=> by simp_rw [vampV]; exact (pale hp hi).2⟩
    filter_upwards [vamp_up n ℓ,vamp_room n ℓ (Nat.pos_of_ne_zero hr),h.price] with i hi hv hx; exact ⟨by rw [Bless,if_neg hr]; exact GaugeTrail hx hi hv,fun h=> (hr h).elim⟩
-- homo via p invariance = local Poly on all off Course. no requirement price for packages separately (need verify when deducing)
def Home (F:Mob G)(h:ℕ): Prop:= ∀ t:ℝ, plow (-(h:ℂ)) t F=F
lemma Home.tad (h:kPrice W){n:ℕ}: Home ( Tad W n) n:= by intro t; rw [move_tad h]; simp [amount]
lemma Home.zero (k:ℕ): Home (G:=G) 0 k:= fun _=> map_zero (plower _ _)
lemma Home.add (h:Home W n)(he:Home S n) : Home (W+S) n:= by intro t; rw [←cert,map_add,cert,cert,h,he]
lemma Home.smul (h:Home W n)(c:ℂ): Home (c • W) n:= by intro t; rw [← cert,map_smul,cert,h]
lemma Home.neg (h: Home W n): Home (-W) n:= by simpa only [neg_one_smul] using h.smul (-1)
lemma Home.sub (h: Home W n)(he:Home S n): Home (W-S) n:= by simp only [sub_eq_add_neg]; exact h.add he.neg
lemma Home.complete (h:Home W n)(hv:kPrice W) : W=Tad W n := by
    have ht :=Home.tad hv (n:=n); have hs : kPrice (W- Tad W n) := fall_sub hv ( tad_price hv n); have hW : Steady0 false (-(n:ℂ)) (W- Tad W n) := fun t m v _=> congr_fun (congr_fun ((h.sub ht) t) m) v; refine sub_eq_zero.mp ( IdEq (decide0 hW hs (show 0<(-(n:ℂ)).re+(n+1:ℕ) by simp) ?_)); intro i hi; by_cases hx:i=n; · subst i; rw [t_minus hv (tad_price hv n),t_already _ hv,if_pos (Eq.refl n),sub_self]; exact fun _ _ _=>rfl
    exact resonance hW hs (by simp [neg_add_eq_zero,Ne.symm hx]) -- ξ includes norm force.
lemma Home.stalled (h:Home W n): Trail W 0 (-(n:ℂ)):= ⟨fun s=>by simp_rw [h _,←cert,map_zero]; exact fun m l=> hasDerivAt_const _ _⟩ -- lint
lemma Home.view (h:Home W n): Wind (fun t=>plow (-(n:ℂ)) t W) atBot W:= by simp_rw [h _]; exact fun _ _=> tendsto_const_nhds
end YM.MS.Hem.Mell
