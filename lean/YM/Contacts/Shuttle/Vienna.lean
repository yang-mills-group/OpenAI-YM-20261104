import YM.Contacts.Shuttle.Canvas
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Shuttle.Pigment
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open MeasureTheory Metric Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Pulse.Spine Origin Trace Trace.Quill
open Milling Milling.Steam Milling.Forge Tensor MultiNext.SignedSource Pattern Tide Morning
open Pulse.Spine.Quill (Balanced)
open scoped Classical Topology BigOperators NNReal Matrix ContDiff
variable {G:Gauge}{h d k r n m u:ℕ}{X Y Z:Type}{L:Side}{s t δ:ℝ≥0}{b c:ℝ}
abbrev Ribbon (X:Type)(k:ℕ):= Cards → Field (Fin k) (Node X)
def Weight (F:Ribbon X k)(d:ℕ)(l: Pulse.Range (Node X))(o:X)(b:ℝ):Prop:= ∀ v:Cards,∀ a:ℝ, 0≤a→ Costs d v a → Rest l (0,o) (F v) (b*a)
namespace Weight
variable {F: Ribbon X k}{f: Cards→ Cohort G}{o:X} {l ε:Pulse.Range (Node X)}
lemma blank (H:Weight F d l o b)(v:Cards): Summable (F v):= by obtain ⟨s,hs,h⟩:= Cards.reach d v; exact (H v s hs h).summ
end Weight
def Clear (F:Ribbon X k)(r:ℕ):Prop := ∀ i<r,∀ v:Cards,Powers.home v.val i→ Trace.Quill.silenced (F v) (r-i)
lemma Clear.across {f:Cards→ Cohort G} (A:∀ v,Tide.Tags (f v)) (hr:r+1 ≤ d+k+2)(ha:h≤d)(hx:r=h+1-k)(hb:d≤n)(hc:d*(d+1)≤u)(hy:∀ v:Cards,∀ i<r,Powers.home v.val i→unreads (f v) d u n (h-i)) : Clear (fun v=> f v k) r:= by
   intro i hi v hv; have ht:= silence (A v) (Nat.le_trans (Nat.sub_le ..) ha) hb hc (hy _ _ hi hv) (show k≤h-i by omega); rwa [show r-i=h-i-k+1 by omega]
-- real linear action under sufficient summability
private abbrev compose (A:X→Y→ℝ)(F: Field (Fin k) X)(y:Fin k→Y)(x:Fin k→X) := F x*∏ i:Fin k,A (x i) (y i)
lemma commerce {A:X→Y→ℝ}{F:Field (Fin k) X}(H:∀ x y, ‖A x y‖ ≤ c)(hc:0 ≤ c)(he: Summable F) (y: Fin k→Y) : Summable (compose A F y):= by
    refine Summable.of_norm ((he.norm.mul_right (c^k)).of_nonneg_of_le (fun _=> norm_nonneg _) fun i=>?_ ); unfold compose; rw [norm_mul, norm_prod]; exact mul_le_mul_of_nonneg_left ((prod_le_prod (g:=fun _=> c) (fun _ _=> norm_nonneg _) (fun _ _=> H _ _)).trans_eq (by simp)) (norm_nonneg _)
namespace Local
variable {F:Ribbon X k}{R: Cross L X Y}
abbrev rotate {L:Side} (z : Cover)(y:E4) (p:Cards) := Cards.onRoute y ((L.val:ℝ)⁻¹) p -- L implicit binder unused? declare (L)
abbrev Bery (R:Cross L X Y)(z:Cover)(y:E4)(F: Ribbon X k)(p:Cards):= wreath z (install R) (F (rotate (L:=L) z y p))
variable {x:X}{y:Y}{z: Cover}{w:E4}
private lemma plate (H:∀ a, Balanced (install R a) (hook t n L a) c) : ∀ i v, ‖install R i v‖ ≤ c := fun i v=> le_trans (le_mul_of_one_le_left (norm_nonneg _) (Spine.mist_one (σ:=t) (n:=n) (a:=size (v.1-rent L i.1)) (Nat.cast_nonneg _))) (budget_single (H i) v)
private def claw (d n r k:ℕ)(c:ℝ)(δ:ℝ≥0) := mist δ n 6*(r+1)*(k+1:ℝ)^n*c^k -- d dummy
-- charge head forecasts ready for ALPHA preblock constants
variable [Fintype X]
lemma bargain (d n k r:ℕ)(c:ℝ)(δ:ℝ≥0)(hc:0≤ c)(hn:r ≤ n)(hr:r ≤ d): ∃ B≥(0:ℝ),∀ (L:Side) (R:Cross L X Y) (s t:ℝ≥0)(F:Ribbon X k)(z:Cover)(x:X)(y:Y)(w:E4), rent L z=0 → Odd L.val → IsLinearMap ℝ F → Clear F r →(∀ (v:List Axis), v.length≤ r →∀ a, Balanced (install (advanceC L R v) a) (hook t n L a) (c/(L.val:ℝ)^(1+v.length))) → t≤δ →(2*(t:ℝ)/(L.val:ℝ))*(k+1) ≤ s → ‖w‖+(L.val:ℝ)⁻¹*4≤4 → ∀ b≥(0:ℝ), Weight F d (bath s n X) x b→ Weight (Bery R z w F) d (bath t n Y) y (B * (L.val:ℝ)⁻¹^(k+r) * b) := by
    let G:= fun i=>claw d n i k c δ; choose! C hC H using fun i=> Cards.planted i d -- order syntax
    let D:ℝ:= G 0* 4^r; let A:=∑ i∈Finset.range r, G (r-i)* C i; have hh i:0≤ G i:= by unfold G claw; have h0:= mist_one (a:=6) (σ:=δ) (n:=n) (by positivity); positivity
    have hD:0≤D:= mul_nonneg (hh 0) (by positivity); have hA:0≤A:= sum_nonneg fun i hi=> mul_nonneg (hh _) (hC i (le_trans (mem_range.mp hi).le hr)); refine ⟨D+A, add_nonneg hD hA,fun L R s t f z x y w hu hL hF hf hR hv he hz b hb ht p a ha hp=>?_⟩
    let l:= (L.val:ℝ)⁻¹; have hl:0 ≤ l:= by unfold l; positivity
    let K(q: Cards):= wreath z (install R) (f q); let phase : Cards:= Cards.onRoute w l p; let Y':= ((0:Cover),y); let Y'':= bath t n Y
    have hs (p:Cards)(i:ℕ)(hi:i ≤ r)(v:ℝ)(hv':0≤ v)(hG:Costs d p v)(hh:silenced (f p) i): Rest Y'' Y' (K p) (G i*l^(k+i)*(b*v)):= by convert (Trace.dawn (y:=y) hu hL (fun t h=> hR t (h.trans hi)) (hi.trans hn) hv he hc (ht p v hv' hG) hh) using 1; unfold G claw hear l; rw [pow_add, div_pow]; simp_rw [inv_pow]; field_simp
    have hl' : l≤1:= inv_le_one_of_one_le₀ (show 1 ≤ (L.val:ℝ) by exact_mod_cast L.property)
    have hq(p:Cards): Summable (f p):=ht.blank _
    let A':= fun u v=> install R (backpack z u) v; have hP : ∀ i q,‖A' i q‖ ≤ c/(L.val:ℝ):= by intro i q; apply plate (n:=n) (t:=t) _ (backpack z i) q; intro a; simpa only [advanceC,List.length_nil,add_zero,pow_one] using hR [] (by simp) a
    have hM:IsLinearMap ℝ K:= by
      constructor
      · intro x y; unfold K; rw [hF.map_add]; ext v; unfold wreath allAt; simp_rw [Pi.add_apply, add_mul]; exact (commerce hP (by positivity) (hq x) v).tsum_add (commerce hP (by positivity) (hq y) v)
      intro a x; unfold K; rw [hF.map_smul]; ext i; unfold wreath allAt; simp [smul_eq_mul, mul_assoc, tsum_mul_left]
    change Rest Y'' Y' (K phase) (((D+A)*l^(k+r)*b)*a)
    cases r with
    | zero=>
      have he' : Costs d phase a:=fun i hi x hx=>(Cards.powCosts hp _ hl hz i hi _ hx).trans (mul_le_of_le_one_right ha (pow_le_one₀ hl hl')); convert hs phase 0 le_rfl a ha he' (fun i j h=> by omega) using 1; dsimp only [D,A,G]; simp only [Finset.range_zero,sum_empty,add_zero,pow_zero,mul_one]; ring
    | succ r=>
      let X i:= Cards.plant i phase; let W:= Finset.range (r+1)
      have hS j (hj:j∈W): Rest Y'' Y' (K (X j)) ((G (r+1-j)* C j)* l^(k+(r+1))*b*a):= by
         have hj:j<r+1:= mem_range.mp hj; have hT:j≤d:= hj.le.trans hr; convert hs _ (r+1-j) (Nat.sub_le ..) _ (mul_nonneg (hC j hT) (mul_nonneg ha (pow_nonneg hl j))) (H j hT p w l a hl ha hz hp) (hf _ hj _ (Cards.colored_plant ..)) using 1; rw [show k+(r+1)=k+(r+1-j)+j from by omega, pow_add _ _ j]; ring
      let Ψ:= Cards.moth r phase; have hΨ: Rest Y'' Y' (K Ψ) (D*l^(k+(r+1))*b*a):= by convert hs Ψ 0 (by omega) _ (mul_nonneg (a:=a*l^(r+1)) (b:=4^(r+1)) (by positivity) (by positivity)) (Cards.meadow hp _ hl hl' ha hz hr) (fun i j hj=>by omega) using 1; unfold D; rw [pow_add _ k (r+1)]; simp; ring
      let u:= (hM.mk' K); have hE : K phase= K Ψ + ∑ i∈W,K (X i):= by rw [show phase= Ψ+∑ i∈W,X i from (sub_add_cancel phase _).symm, hM.map_add]; exact congr_arg _ (map_sum u ..)
      rw [hE]; convert hΨ.add (Rest.sum hS) using 1; unfold A W; simp_rw [add_mul,sum_mul] -- need W issues
end Local
end YM.Contacts.Shuttle.Pigment
