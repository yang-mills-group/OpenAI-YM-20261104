import YM.OPE.Polar.Knobs
import YM.Next.BOUNDARY.Stage
import Mathlib.Data.Fin.Tuple.Sort
/-!
# Along arbitrary axes with reserve
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar
open Function Set Filter MeasureTheory Metric Boundary
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U:Spec.Final C f S) {I : Type}[Fintype I][DecidableEq I]
    (p:I→C.book.Token) (K:Ortho) {m:ℕ} (q:I→ℝ) {x y:I→E4}
local notation "T"=> U.B.waves
-- all unselected contours from actual final
lemma breath : U.B.waves.Breathes := by
    obtain ⟨_,Y,hY⟩:= Next.BOUNDARY.at_contour (Next.BOUNDARY.unselected_pantry (s:=U.room) U.phase) U.realization.allWorld
    rw [← hY]; exact Y.power.1

private def rot (z:E4) := time (Ortho.motion K z)
private def key (x:I→ E4) := rot K ∘ x
structure Reserve (K: Ortho)(x:I→ E4)(q:I→ℝ)(b:ℝ) : Prop where
    opens : ∀ i j: I, i ≠ j → |q i-q j|+b ≤ |time (Ortho.motion K (x i))-time (Ortho.motion K (x j))|
variable {b:ℝ}
lemma Reserve.unique (h:Reserve K x q b) (hv:0<b) : Injective (key K x) := by
    intro i j H; by_contra hi; have hx:0 < |key K x i-key K x j|:= lt_of_lt_of_le (add_pos_of_nonneg_of_pos (abs_nonneg _) hv) (h.opens i j hi); exact absurd H (sub_ne_zero.mp (abs_pos.mp hx))
private lemma perm_order (f:I→ℝ)(h:Injective f) : ∃ e: Fin (Fintype.card I)≃ I, StrictMono (f ∘ e):= by
    let g:= f ∘ runNames I; let v:= Tuple.sort g; have he:Monotone (g ∘ v):= Tuple.monotone_sort _; exact ⟨v.trans (runNames I), he.strictMono_of_injective (h.comp ((v.trans (runNames I)).injective))⟩
private lemma breath_price (p: Fin m→ S.Union): ∃ c k, 0 ≤ c ∧ ∀ (a:ℝ), 0<a → a ≤ 1→ ∀ (z : Times m)(x:SpacePoints m), broad (fun i=> (z i).im) a → ‖(T).F m z x p‖ ≤ c * a⁻¹^k:=by
    obtain ⟨k,c,hc,h⟩:= breath U m p; refine ⟨c,k,hc,fun a ha hh z x hz=>?_⟩; let y:= fun i=>(z i).im; let u:= place x fun i=>(z i).re; have h := h y a ⟨ha,hh⟩ hz u; unfold Waves.restricted at h; rw [show shift u y=z from funext (fun i=>by simp [shift,u,place,y]), show trace u=x from funext (fun i=>by simp [trace,u,place])] at h; exact h

-- Keep offsets condition local, widths q precise (can be zero or rigid groups)
def along (x:I→E4)(K:Ortho)(q:I→ℝ)(r:ℝ): I→ E4:= fun i=> x i+(r*q i) • (forwards K).val
private lemma along_rot (x:I→ E4)(r:ℝ)(i:I) : key K (along x K q r) i = key K x i + r*q i:= by unfold along key rot time; simp only [comp_apply, map_add,map_smul,forwards,LinearIsometryEquiv.apply_symm_apply]; simp
lemma along_zero (x:I→ E4) : along x K q 0=x:=funext fun _=>by simp [along]
private lemma along_spatial (x:I→E4)(r:ℝ) (i:I): spatial (Ortho.motion K (along x K q r i))=spatial (Ortho.motion K (x i)):= by
    unfold along; simp only [map_add,map_smul,forwards,LinearIsometryEquiv.apply_symm_apply]; ext a; have hh:a.castSucc ≠ timeAxis:= Fin.castSucc_ne_last a; simp only [spatial,WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply,basis_eq,if_neg hh,smul_zero,add_zero]
private lemma Reserve.broad (h:Reserve K x q b) (r : ℝ) (he: |r|≤1)(e:Fin m≃ I)(ht:StrictMono (key K x ∘ e)) : broad ((key K (along x K q r)) ∘ e) b:=by
    intro i j hij; have hz := h.opens (e j) (e i) (e.injective.ne hij.ne'); change _ ≤ |key K x _-key K x _| at hz; rw [abs_of_nonneg (sub_nonneg.mpr ((show key K x (e i) ≤ key K x (e j) from (ht hij|>.le))))] at hz; have hu : |r*(q (e j)-q (e i))| ≤ |q (e j)-q (e i)|:= by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) he
    simp only [comp_apply]; rw [along_rot,along_rot]; linarith only [hz, neg_le_of_abs_le hu]
private lemma Reserve.clear {K:Ortho}{q:I→ℝ}(h:Reserve K x q b)(hv:0<b) {r : ℝ}(he:|r| ≤ 1): Injective (along x K q r):= by
    obtain ⟨e,hh⟩:= perm_order (key K x) (Reserve.unique K q h hv); have ht:StrictMono (key K (along x K q r) ∘ e):=fun i j hij => sub_pos.mp (hv.trans_le (h.broad K q r he e hh i j hij)) -- field notation?
    intro i j Hi; obtain ⟨i,rfl⟩:=e.surjective i; obtain ⟨j,rfl⟩:=e.surjective j; exact congr_arg e (ht.injective (congr_arg (rot K) Hi))
def rotating (e:Fin m≃I) : Fin m→ S.Tag:= (U.sector.turns.label K) ∘ S.classTokens ∘ p ∘ e
def pinned (e:Fin m≃I) : Fin m→ S.Union:= fun i=>S.pin (rotating U p K e i).1 (rotating U p K e i).2
private lemma oriented_time (v:I→ E4)(p:I→C.book.Token)(e:Fin m≃I)(hv:StrictMono ((key K v) ∘ e)) : let x:= points ((Ortho.motion K : E4→E4) ∘ v ∘ e); (T|>.F m (fun i=> (time (x i):ℂ)*Complex.I) (trace x) (pinned U p K e))= observe S v p:=by
    intro x'; let y:= key K v ∘ e; have hf : place (trace x') y=x' := by ext1 i; apply position_eta
    have hp:= U.realization.allWorld.heat.roots m (rotating U p K e) (trace x') y hv; rw [hf] at hp; have hZ:Injective v:=by
       intro i j Hi; obtain ⟨i,rfl⟩:= e.surjective i; obtain ⟨j,rfl⟩:= e.surjective j; exact congr_arg e (hv.injective (congr_arg (rot K) Hi))
    have hx : points (v ∘ e) ∈ conf _:= hZ.comp e.injective; have hr:= U.room.kernel.laws.toSymmetric
    rw [← perm_observe S hr e p hZ , (show observe S (v ∘ e) (p ∘ e)=_ from named_fin S hr (x:=points _) (p ∘ e) hx)]; have hz:= S.at_project S hr (fun _=>le_rfl) hx (p ∘ e); change _ = _ at hp; refine hp.trans (?_); exact (U.phase.transport.motion _ (S.classTokens ∘ p ∘ e) _ hx K).trans hz

include U
lemma reserve_price : ∃ c d, 0 ≤ c ∧ ∀ x:I→ E4, ∀ q:I→ℝ, ∀ b:ℝ,0<b→ b ≤1→ Reserve K x q b→ ∃ F:ℂ→ℂ,
    (∀ z∈closedBall (0:ℂ) 1, DifferentiableAt ℂ F z) ∧ (∀ z:ℝ, |z|≤ 1→ Injective (along x K q z) ∧ F (z:ℂ)=observe S (along x K q z) p) ∧ ∀ z∈closedBall (0:ℂ) 1, ‖F z‖ ≤ c*b⁻¹^d:=by
    let n:= Fintype.card I; choose c d hc hd using fun e: Fin n≃I=> breath_price U (pinned U p K e)
    let Z:= Fin n≃I; refine ⟨∑ x:Z,c x, ∑ x:Z,d x, Finset.sum_nonneg fun i _=>hc _,fun x q b hb hb' h=>?_⟩; obtain ⟨e,he⟩:= perm_order (key K x) (h.unique K q hb)
    let V (r):= along x K q r; let y:= key K x; let g (z:ℂ) (i:Fin n):= ((y (e i):ℂ)+z*(q (e i):ℂ))* Complex.I; let X(i):= spatial (Ortho.motion K (x (e i))); let F(z:ℂ):= (T).F n (g z) X (pinned U p K e);
    have hx (z:ℂ) (i: Fin n): (g z i).im= key K (V z.re) (e i):=by unfold V; rw [along_rot]; simp [g,y];
    have hz(z:ℂ)(hu:z∈ closedBall (0:ℂ) 1): broad (fun i=>(g z i).im) b:=by
       simp_rw [hx]; exact h.broad K q z.re ((Complex.abs_re_le_norm _).trans (mem_closedBall_zero_iff.mp hu)) e he
    refine ⟨F,fun z hu=> ((U.realization.allWorld.heat.hol n _ X _ (?_)).differentiableAt ( (open_strict n).mem_nhds (?_))).comp (f:=g) z (by unfold g; fun_prop),fun r hr=>?_,fun z hu=>?_⟩
    · exact fun i j hij=>sub_pos.mp (hb.trans_le (hz z hu _ _ hij))
    · exact fun i j hij=>sub_pos.mp (hb.trans_le (hz z hu _ _ hij)) -- repeated synthetic opaque?
    · have hE: StrictMono (key K (V r) ∘ e):= fun i j hij=>sub_pos.mp (hb.trans_le (h.broad K q r hr e he _ _ hij)); refine ⟨Reserve.clear h hb hr,?_⟩
      let x':= points ((Ortho.motion K : E4→E4) ∘ V r ∘ e); rw [← oriented_time U K (V r) p e hE]; unfold F; rw [show X= trace x' from (funext fun i=> (along_spatial K q x r (e i)).symm), show g (r:ℂ)=(fun i=>↑(time (x' i))*Complex.I) from ?_]
      exact funext fun i=>by change g (r:ℂ) i=↑(key K (along x K q r) (e i))*_; rw [along_rot]; simp [g,y]
    refine (hd e b hb hb' (g z) X (hz z hu)).trans ?_; exact mul_le_mul (Finset.single_le_sum (fun i _=>hc i) (Finset.mem_univ e)) (pow_le_pow_right₀ ((one_le_inv₀ hb).mpr hb') (Finset.single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (Finset.mem_univ e))) (by positivity) (Finset.sum_nonneg fun i _=>hc i)
end YM.OPE.Polar
