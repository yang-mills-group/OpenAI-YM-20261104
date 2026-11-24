import YM.LocalLTE.Concert.Beacon
import YM.LocalLTE.Concert.Eight
import YM.LocalLTE.Pond.Cleats
/-!
# Lift of any supplied true probe and prepaid local presentation
Budget adapters. Preserve all physical. No trajectory here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side} (P:Rep G n)
variable {V α :Type}[DecidableEq V]{R:Census V} (X:Layers P R α)
variable [Fintype α][Nonempty V] (φ:α→ Config G n→ℂ)
local notation "Q'"=> posta P R X
-- Truth decomposition. Supporting slip.Native!
-- *Pretends* catalogue from its owner Layout, not anticipating ANY evolution
-- coefficients.
-- erase K entries but keep supports and tag metadata
abbrev crystal : Bands R P:= {(posta P R X) with H:=unpin φ 0,entries:=0}
abbrev thaw : Bands R P:= {(posta P R X) with H:= unpin (X.H-φ) 0,units:=0}
local notation "M'"=>crystal P X φ
local notation "B'"=> thaw P X φ
local notation "x'"=>unpin φ 0
local notation "y'"=>unpin (X.H-φ) 0
lemma cleansed : Fan.Tabs P R (posta P R X) (crystal P X φ) (thaw P X φ):=by
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩; funext i
    change unpin X.H _ i - x' i= y' i; by_cases h:i∈Set.range (pin:α→ℕ); · obtain ⟨p,rfl⟩:=h; rw [unpin_pin,unpin_pin,unpin_pin]; rfl
    simp only [unpin_blank _ _ h,sub_zero]
local notation "W"=> P.p
variable {v:V→ℝ}{a b c d u k:ℝ}
variable (hp:∀ j, P.p.Regular (X.region j) (φ j))(hf:∀ j,P.p.Regular (X.region j) (X.H j-φ j))
include hp hf
lemma starsV(hy: (posta P R X).Active) : (crystal P X φ).Active ∧ (thaw P X φ).Active:=by
    have h (f:α→ Config G n→ℂ) (h:∀ j,P.p.Regular (X.region j) (f j)) (i:ℕ) : P.p.Regular ((Q').support i) (unpin f 0 i):=by
       change P.p.Regular (unpin X.region Finset.univ i) _; by_cases he:i∈Set.range (pin:α→ℕ); · obtain ⟨j,rfl⟩:=he; rw [unpin_pin,unpin_pin]; exact h j
       rw [unpin_blank f _ he]; exact (show unpin X.H 0 i=(0:Config G n→ℂ) from unpin_blank _ _ he) ▸ (show P.p.Regular _ (unpin X.H 0 i) from hy.regular i)
    refine ⟨⟨hy.proper,hy.pins,h φ hp,hy.occurs,fun i j h=> False.elim (h rfl),fun _ _ _ _ _ _=>rfl,fun i j V h=>False.elim (h rfl),fun _ _=>measurable_const,fun _ _ _ _=>rfl⟩,⟨hy.proper,hy.pins,h (X.H-φ) hf,hy.occurs,hy.retained,hy.inspects,hy.keeps,hy.meas,hy.invi⟩⟩ -- syntax q' etc
omit hf hp
lemma evenCap (hv:∀ i:V,0<v i)(m:α→ℝ)(hm:∀ i:α,0≤ m i)(hq:∀ i j,j∈(X.tag i).val → P.p.supBounds (X.origins j) (X.region i) (φ i) (m i))(he:∀j:V,SumBudget (fun i=>if j∈ (X.tag i).val then Poly.toll v (X.tag i)*P.p.mass (X.region i) (m i) else 0) k): let s:=unpin m 0; (∀ i:ℕ,0≤ s i∧∀ j∈ ((Q').rays i).val,P.p.supBounds ((Q').origins j) ((Q').support i) (x' i) (s i))∧ ∀ j:V,SumBudget (fun i=> if j∈ ((Q').rays i).val then Poly.toll v ((Q').rays i)*P.p.mass ((Q').support i) (s i) else 0) k :=by
    intro s
    have hx i: (Q').rays i=unpin X.tag (R.fire (Classical.arbitrary V)) i:=rfl
    have hy i: (Q').support i= unpin X.region Finset.univ i:=rfl
    have h(i):0≤ s i:=by
       by_cases h:i∈Set.range (pin:α→ℕ); swap; · exact (unpin_blank _ _ h).ge
       obtain ⟨p,rfl⟩:=h; exact ((unpin_pin m 0 p).symm ▸ hm p : 0≤ unpin m 0 _)
    refine ⟨fun i=> ⟨h i,?_⟩,fun j=>?_⟩
    · rw [hx,hy]; unfold s; by_cases h:i∈Set.range (pin:α→ℕ); swap; · rw [unpin_blank X.region _ h,unpin_blank φ _ h,unpin_blank m _ h]; exact fun j _=> Extra.Multi.supBounds_zero ..
      obtain ⟨p,rfl⟩:=h; rw [unpin_pin,unpin_pin,unpin_pin,unpin_pin]; exact hq p
    simp_rw [hx,hy]; unfold s; refine budget_image pin_injective injective_id ?_ ?_ (he j) ?_
    · intro i; split; exact mul_nonneg (Poly.worth hv _).le (mul_nonneg (Real.exp_nonneg _) (h i)); rfl
    · intro i hi; split; next h=> simp [BudgetPoint.mass,unpin_blank m _ hi]
      rfl
    intro i; simp only [unpin_pin,id_eq,le_refl]
lemma pollen (h:(posta P R X).Radial v a b c d)(hz:0≤c)(m n':α→ℝ)(hm:∀ i:α,0≤ m i)(hM:∀ i:α,0≤n' i)
    (hq:∀ i j,j∈(X.tag i).val → P.p.supBounds (X.origins j) (X.region i) (φ i) (m i))
    (hq':∀ i j,j∈(X.tag i).val→ P.p.supBounds (X.origins j) (X.region i) (X.H i-φ i) (n' i))
    (he:∀j:V,SumBudget (fun i=>if j∈ (X.tag i).val then Poly.toll v (X.tag i)*P.p.mass (X.region i) (m i) else 0) u)
    (he':∀j:V,SumBudget (fun i=>if j∈ (X.tag i).val then Poly.toll v (X.tag i)*P.p.mass (X.region i) (n' i) else 0) k):
    (crystal P X φ).Radial v a u c d ∧ (thaw P X φ).Radial v 0 k c d:=by
    refine ⟨⟨h.pure,h.localU,h.factor, ⟨_,evenCap P X φ h.pure m hm hq he⟩,?_⟩, ⟨h.pure,fun i=>?_,h.factor,⟨_,evenCap P X (X.H-φ) h.pure n' hM hq' he'⟩, h.hits⟩⟩
    · refine ⟨0,fun i j=> ⟨le_rfl,fun x=>?_⟩,fun i=>?_⟩
      · change ‖(0:ℂ)‖ ≤ 0; rw [norm_zero]
      simp_rw [Pi.zero_apply,BudgetPoint.mass,mul_zero,ite_self]; exact ⟨fun i=> le_rfl,summable_zero, (by simpa using mul_nonneg hz h.factor.le)⟩
    simp
-- transport L marker phases
open FrameBox Grove Cabana
open AnalyticBridge VerifiedReset Collection
lemma appeal {d b:ℕ}{κ:ℝ} (h: ∀ i,∃ x∈ X.region i,X.region i⊆ Animals.neighbors b x∧ ∃ m ≤ b,∃ Y: FrameBox.Grove x,∀ k:Bool,Collection.Price.Replicated Y m κ (d+1) (scaleQ k ∘ φ i)) : Port.Shine R (crystal P X φ) d b κ :=by
    refine ⟨fun i hi=>?_⟩; change x' i≠0 at hi; by_cases hp: i∈Set.range (pin:α→ℕ); swap; ·exact (hi (unpin_blank _ _ hp)).elim
    obtain ⟨p,rfl⟩:=hp; obtain ⟨x,hE,hX,v,hV,Y,hT⟩:=h p; have he: (M').support (pin p)=X.region p:=unpin_pin _ _ _
    rw [he]; refine ⟨x,hE,hX,v,hV,Y,fun k=> ?_⟩; rw [show (M').H (pin p)=_ from unpin_pin φ 0 p]; exact hT k
end YM.LocalLTE.Port
