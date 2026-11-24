import YM.Integration.WilsonPhysicalExteriorUVStory
import YM.MS.Vane.Trigger

/-! The actual signed temporal flow on the original Markov/DR source rows.
The original fields, their native laws and differential equations are kept.
Resolved spatial pairs may be arbitrarily far apart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorResolved
open Set Function Filter Finset Metric MeasureTheory Real
open YM.MS
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve City Vane Land Menus
open scoped Topology ContDiff Interval Classical

structure Source {G : Gauge} {I W : Type} (K L : Planet G I) (P : Geo I)
    (x : Position W I) (b : Bool) (F : Site G I) (A : W→Site G I) (R : W→ℕ) : Prop where
  plot : WilsonPhysicalExteriorUVStory.Resolved P x
  ground : Stage K L P b
  energy i : 0 < i → Tip P b true 4 (F i)
  obey i n : Tip P b false (R i) (A i n)
  register s : Ven (fun _=>planeF) K L F (A s)

abbrev Pair {I : Type} (P : Geo I) (ξ : I→QP) : Prop :=
  ∃ t : ℝ, 0<t ∧ ∀ i, P.roots i≤t*‖ξ i‖

section
variable { I E J:Type}{G:Gauge}[LinearOrder J] {s:Finset J}{P:Geo I}{R: J→ℕ}{x:Position J I}{K L:Planet G I}{b:Bool} {X H: Site G I}{A:J→Site G I}{Y:Dance G I J}{n:ℕ}{μ:I→Measure QP}
variable (h:Source K L P x b X A R)(hv: Fields x (fun _=>planeF) K L X A Y)
local notation "m0"=> (fun (_:I)=>planeF)
include h

lemma formal : ∃ Y, Fields x m0 K L X A Y :=
  ⟨_,(WilsonPhysicalExteriorUVStory.fields h.ground h.plot h.energy
    (fun i k=>⟨_,h.obey i k⟩)).1⟩
include hv
lemma emerged (hp:2≤s.card)(n:ℕ) : Came P b (Y s n) := by
  obtain ⟨hF,hW⟩ := WilsonPhysicalExteriorUVStory.fields h.ground h.plot h.energy (fun i k=>⟨_,h.obey i k⟩)
  rw [perfect hv hF]; exact hW s hp n
lemma tip0 (hs:s.Nonempty): ∃ a:ℕ,Tip P b false a ( Y s n ):= by
    by_cases he: s.card ≥ 2; · exact ⟨0,tipby (emerged h hv he n) _ ⟩;
    obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp ( show s.card=1 from by obtain he':= Finset.card_pos.mpr hs; omega ); rw [hv.2.1]; exact ⟨_,h.obey i n⟩
lemma founded (hp:s.Nonempty)(n:ℕ): collect ( Y s n ) ∧ Warm ( Y s n ) false:= by obtain ⟨v,hm⟩:= tip0 h hv (n:=n) hp; exact ⟨hm.1,hm.2.1⟩
lemma hosp (hp:s.Nonempty)(n:ℕ): Warm ( Src x m0 K L X Y s n ) false:= by
    refine CabinF.warm_zip ( warm_sum (F:=fun i=> expJ _ _ _) _ (fun i hi=>?_)) (warm_sum _ (fun i hi=>warm_sum _ (fun j hj=>?_))) -- infer F size
    · exact walk_tree h.ground.pinC ( h.energy ( n-i ) (by obtain hx: i<n:= ( Finset.mem_Ico.mp hi ).2; omega)|>.2.1 ) ( founded h hv hp i |>.2 )
    exact warmJoin (fun _=>Coherent) h.ground.pool (founded h hv ( n_small hi |>.2.1 ) _ |>.2 ) ( founded h hv ( n_small hi|>.2.2.1 ) _|>.2 )
lemma winter (hp:s.Nonempty)(n:ℕ): Warm (rhs x m0 K L X Y s n) false:= CabinF.warm_zip ( warmCycle (fun _=> Coherent) h.ground.pool ( founded h hv hp n|>.2 )) ( hosp h hv hp n )
lemma motion (hp:s.Nonempty)(n:ℕ) : Fits false ( Y s n ) (rhs x m0 K L X Y s n):= by
    obtain hh:= winter h hv hp n; refine ⟨ hh.walk, ?_⟩; intro i w hw t; by_cases hx:s.card<2
    · obtain ⟨k,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain he:= Finset.card_pos.mpr hp; omega); have hc: picks ({k}:Finset J)=∅:= Finset.eq_empty_iff_forall_notMem.mpr fun i hi=> clips (by simp) hi; unfold rhs Src multi; rw [hc,hv.2.1]; rw [Finset.sum_empty,add_zero]; exact h.register k n |>.motion i w t
    let H:=rhs x m0 K L X Y s n; obtain ⟨hu,hW,hM⟩:= hv.2.2 s (le_of_not_gt hx) n; change Y s n=river H at hM; have hx:(fun t:ℝ=> Y s n i t w)=fun t:ℝ=> river H i 0 w+∫ s in 0..t,H i s w:= funext fun t=> by rw [hM]; exact swamp hW i t 0 hw
    rw [hx]; exact ( hfun (hh.walk _ _ hw) t ).const_add _
end

section
variable {I : Type} {G : Gauge} {P : Geo I} {S : Belt I} {K : Planet G I}
variable {F H : Glade G I} {ξ : I→QP} {a b c : S.time→ℝ}

lemma river_bound (hξ : Pair P ξ) (he : Flow S K a)
    (hf : Here false true S F b) (hh : Here false true S H c)
    (ha : nn a) (hb : nn b) (hc : nn c) (j : ℕ) :
    Here false false S (regionC (fun _=>planeF) ξ K F H)
      (fun p=>a p*(b p*c p)*(S.price.length p/P.roots p.1)^j) := by
  obtain ⟨t,ht,hξ⟩ := hξ
  apply WilsonPhysicalExteriorUVStory.constant_price (C:=t^j) (pow_pos ht j)
  apply Lease.sticks (WilsonPhysicalExteriorMixedKernel.kernel S.price (fun p=>ξ p.1) he hf hh ha hb hc j)
  intro p
  have h₁ := S.price.pos p
  have h₂ : 0<P.roots p.1 := exp_pos _
  have hh : S.price.length p/max (S.price.length p) ‖ξ p.1‖ ≤ S.price.length p/P.roots p.1*t := by
    apply (div_le_iff₀ (h₁.trans_le (le_max_left ..))).mpr
    calc
      _ = (S.price.length p/P.roots p.1)*P.roots p.1 := (div_mul_cancel₀ _ h₂.ne').symm
      _ ≤ (S.price.length p/P.roots p.1)*(t*max (S.price.length p) ‖ξ p.1‖) :=
        mul_le_mul_of_nonneg_left ((hξ p.1).trans (mul_le_mul_of_nonneg_left (le_max_right ..) ht.le))
          (div_nonneg h₁.le h₂.le)
      _ = _ := by ring
  calc
    _ ≤ (a p*(b p*c p))*(S.price.length p/P.roots p.1*t)^j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (div_nonneg h₁.le (h₁.le.trans (le_max_left ..))) hh _) (mul_nonneg (ha p) (mul_nonneg (hb p) (hc p)))
    _ = _ := by rw [mul_pow,mul_assoc (a p*(b p*c p))]

lemma lighting {n k : ℕ} (hs : Sheet (Gulf P).price 1 (plug K)) (hx : Pair P ξ)
    (hp : Here false true (Gulf P) F (rateS (Gulf P) n))
    (he : Here false true (Gulf P) H (rateS (Gulf P) k)) :
    Bud P (n+k) 0 (regionC (fun _=>planeF) ξ K F H) := by
  intro j
  apply Lease.sticks (river_bound hx hs hp he (fun _=>zero_le_one) (rateC _ _) (rateC _ _) j)
  intro p
  rw [dotzero,dotzero,roll,Pi.one_apply,one_mul,← stock,zero_add,add_zero,Nat.zero_add]

lemma fossil (hk : Flow S K a) (hp : Here false true S F b) (hf : Here false true S H c)
    (hb : nn b) (hc : nn c) (ha : nn a) : Here false false S (regionC (fun _=>planeF) ξ K F H) (a*(b*c)) := by
  apply Lease.sticks (WilsonPhysicalExteriorMixedKernel.kernel S.price (fun p=>ξ p.1) hk hp hf ha hb hc 0)
  intro p; simp only [pow_zero,mul_one,Pi.mul_apply,le_refl]

end
end YM.Integration.WilsonPhysicalExteriorResolved
