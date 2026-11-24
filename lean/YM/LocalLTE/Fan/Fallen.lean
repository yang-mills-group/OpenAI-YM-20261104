import YM.LocalLTE.Fan.Choice
/-! Thin ensemble on actual H. Rank pricing at vertices. α thresholds monotonic. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Field
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained Gas Ursell
variable {v z r W w s t y η γ B a μ b C C' q X Y : ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
section scalar
variable {x: ℝ}
lemma coefficientBound (ι:Type)[Fintype ι][DecidableEq ι]:∃ A:ℝ,0≤A∧∀ (β: Type*) (R:β → β→Prop)(p:ι→β), |Ursell.coefficient R p| ≤ A:= by
   let f (S:Push.AbsoluteSums.Graph.Network ι):=|Push.AbsoluteSums.Graph.mass S|
   exact ⟨∑ s,f s, Finset.sum_nonneg fun _ _=> abs_nonneg _,fun _ R p=> single_le_sum (f:=f) (fun _ _=>abs_nonneg _) (mem_univ (Ursell.pot R p))⟩ -- edit namespace
end scalar
variable (H: Cash W t μ L Q o a T R)
variable (K: Captain H j C v z r Y C' w B q m χ)
section body
variable {q:ℕ}
abbrev Slots (q:ℕ) := Option (Fin q)
local notation "Z"=> Option (Fin q)
local notation "VF"=> Finset (Veil c f)
variable (D: Slots q→ Finset (Veil c f)) (u: Ursell.Tuple H.ThinP q)
abbrev Gains (n:ℕ):= (i:Slots q)→ LevelsΛ (D i) n
def built (w:Gains D N)(u:Veil c f→ℝ):= ∑ i, tones (D i) u (w i)
def lace (p: Disk G c)(z:Gains D N)(χ:Chi):= ∏ i, perLeaf χ (D i) H (z i) p
def oiled (A:Veil c f →ℝ)(i: Slots q):= ∏ j∈ D i,A j
def stock (A:Veil c f →ℝ):= ∏ i: Option (Fin q), (Field.oiled D A i)
lemma rankH (i) (h:(D i).card≤ M)(hN : 1≤N): Fintype.card (LevelsΛ (D i) N)≤ N^M:= by
   unfold LevelsΛ; rw [Fintype.card_fun,Fintype.card_coe,Fintype.card_fin]; gcongr
lemma charged (h:∀ i,(D i).card≤ M)(hN:1≤N): Fintype.card (Gains D N) ≤ (N^M)^(q+1):=by
   apply le_trans (b:= ∏ i:Slots q,N^M)
   · unfold Gains; rw [Fintype.card_pi]; exact prod_le_prod' fun i _=>rankH D _ (h i) hN
   exact le_of_eq (by simp [Slots])
lemma oil_nonneg {A: Veil c f→ℝ}(h:∀ i,∀ j∈D i,0≤A j) (i):0≤ Field.oiled D A i:= prod_nonneg (h _)
lemma quiet (w:Gains D N)(q:ℕ→ℕ)(i): tones (D i) (levy q) (w i) ≤ 0:= Finset.sum_nonpos fun j _=> mul_nonpos_of_nonpos_of_nonneg ((financial _ _ _ _).trans (by unfold mini; norm_num)) (Nat.cast_nonneg _)
-- alpha threshold tests. Any heavy anc, q≥ all. Cost includes one growth per head at N. 
private def wash (u:ℕ→ℕ)(v:Veil c f) (p:ℕ):ℕ:= Sum.elim (fun i=> u i * p) (fun _=>0) v
lemma extendH (z: Gains D N) (u:ℕ→ℕ) {p:ℕ} (h:∃ i k, Sum.inl k∈ D i)(hE:∀ i k, Sum.inl k∈ D i→ u k≤ p)
    (hp: chip (p+1) - 10*slack ≤ built D z (levy u)) : built D z (jumpP u) - (1/2:ℝ)*(pie p+1:ℕ) ≤ chip (p+1)-20*slack := by
  -- counting m slots without injections
  let w i j:= ((z i j).val+1)
  let α:Type := Sigma (fun i=> ↥(D i))
  let q' (a:α):= w a.1 a.2; let s (a:α):= Sum.elim (fun _=> q' a) (fun _=>0) a.2.val
  let τ(a:α):= Sum.elim (fun _=>0) (fun _=>q' a) a.2.val
  let r(a:α):= wash u a.2.val (q' a)
  letI: Fintype α:=inferInstanceAs (Fintype (Sigma (fun i=> ↥(D i))))
  let a := ∑ i,s i; let b:=∑ i,τ i; let d:=∑ i,r i
  let A:ℝ:= built D z (levy u); let B:ℝ:= built D z (jumpP u)
  have heκ (f:α→ℝ) : ∑ i:α,f i=∑ i:Slots q, ∑ j:↥(D i), f ⟨i,j⟩ := Fintype.sum_sigma (fun i:Sigma (fun i=> ↥(D i))=> f i)
  have hA:A = (-(11/10)+slack)*a + mini*b- (1/100:ℝ)*d:= by
     unfold A a b d -- edit
     simp only [Nat.cast_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
     rw [heκ]
     refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_
     cases he:j.val
     all_goals simp only [q',s,τ,r,wash,levy,he,Sum.elim,chip,w]; push_cast; ring
  have hB:B = A + (4+slack)*a+3*(b:ℝ)+ (1/2:ℝ)*d:= by
     unfold A B built tones a b d -- maybe indentation
     simp only [Nat.cast_sum,Finset.mul_sum]
     rw [heκ, heκ, heκ]; rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
     rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
     cases hp:j.val
     all_goals simp only [s,r,τ,wash,hp,Sum.elim,jumpP, q',w,pie]; push_cast; ring
  obtain ⟨i,l,hL⟩:= h; let i':α := ⟨i,⟨Sum.inl l,hL⟩⟩ -- edit
  have hh : s i' = q' i':= rfl
  have ha': s i' ≤ a:= single_le_sum (f:=s) (fun _ _=> Nat.zero_le _) (mem_univ i')
  have hs: 1 ≤ s i':=hh.symm ▸ Nat.le_add_left 1 _
  have ha:1 ≤ a:= hs.trans ha'; change _≤A at hp; change B-_ ≤ _
  by_cases he:b≥1 ∨ a≥ 2
  · rcases he with he|he <;> unfold chip slack mini pie at * -- edit
    · push_cast at *; linarith only [hB,hA, hp, show (1:ℝ)≤(b:ℝ) from by exact_mod_cast he, show (1:ℝ)≤(a:ℝ) from by exact_mod_cast ha]
    push_cast at *; linarith only [hB,hA,hp,Nat.cast_nonneg (α:=ℝ) b, show (2:ℝ)≤(a:ℝ) from by exact_mod_cast he]
  push Not at he; have ha : a=1:=by omega
  have hb : b=0:=by omega
  have hd : d=u l := by
     refine Eq.trans (Finset.sum_eq_single i' ?_ (by simp)) ?_
     · intro p hp h
       have hz (j:α) : s j=0→ r j=0:=by
         unfold s r wash; cases h:j.2.val <;>simp [*]
       apply hz; by_contra hh; have h0 : s i'+s p≤a:= by
         apply le_trans (b:=∑ j∈{i',p},s j)
         · simp [Ne.symm h]
         exact Finset.sum_le_sum_of_subset (subset_univ _) -- edit
       omega
     have he: q' i'=1:= le_antisymm (hh ▸ (ha ▸ ha')) (hh ▸ hs)
     change u l * _ = _; rw [he,mul_one] -- edit
  rw [ha,hb,hd] at hA hB; unfold slack chip pie at *; push_cast at *; simp only [mul_zero,add_zero] at * -- edit
  linarith only [hB,hA,show (u l:ℝ)≤ p from by exact_mod_cast (hE i l hL)]
end body
end YM.LocalLTE.Fan.Field
