import YM.LocalLTE.Sail.Mixed
/-! Formation of analytic plant call from hereditary purchases. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Filter Function Finset Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open GridApprox.Nil Extra.Trajectories Progress.DirectedRecipe MergeProof Menu Accent Push.AbsoluteSums
open Overlay Planned.GuardedAtom Guard LocalLTE.XPhase
open PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V J : Type} [DecidableEq V] [Fintype V] [Fintype J]
variable (B:Census V) {G:Gauge}{n n':Side} {P:Rep G n}{P':Rep G n'}
variable (I A D : Bands B P) -- mixed payload on supplied Appendix. CFG in coasts
variable (H:Support n→ Config G n→Poly B)(K: Box n→ Config G n→Poly B) (hr: Carton I.origins H K P.p.threshold)
     (hc: ∀ U: Config G n,(∑' j,I.ray j U)=∑ i,H i U)(ht:XPhase.lightF B P I=K)
     {a b X Y d ε k y:ℝ} {m l j S₀:ℕ} (w:V→ℝ)
     (hA:A.Active)(hD:D.Active)(hP:A.Radial w a b X ε)(hQ:D.Radial w 0 Y d ε)(hX:Fan.Tabs P B I A D)(hE:Port.Shine B A m l k)(hm:HasSlots P.p P.activities)
variable {h:V→ℕ} {b₁:V→ℕ} (F: V→ Config G n→ℂ)(G0:V→Res G n)(C:V→ Res G n') (v:V→ℂ)
    {t₁ q₁ ξ₁ y₁: V→ℝ} (T: StepData n' n)(L : GaugeDoor P P') {β σ κ η t x z:ℝ}
variable (hJ:∀ i, h i ≤ b₁ i)(hG:∀ i, b₁ i ≤ m)(hV:Fintype.card V≤ S₀)
    (hy:1≤ y)(hz:∀ i,w i*q₁ i≤ z)(hl:m ≤ j)(hh:S₀ ≤ j)(hk:S₀*m ≤ j)
variable (hR:P.Lawful t β x η κ)(hT:SoundDoor T L)(hL:Tunes L)(hv:∀ i,∃ X:Set Wing,X.Finite ∧ XPre.Circuit X L (h i) k (b₁ i) l (I.origins i) (T.ratio.parent (I.origins i)) 1 (F i) (G0 i) (C i) (v i) (t₁ i) (q₁ i) (ξ₁ i)) (hw:∀ i,0<y₁ i)
local notation "t₀"=> Port.capacity P.p V b Y ε d y l
local notation "x₀"=> Accent.restore P F G0 H K
local notation "o"=> I.origins
local notation "o'"=> T.ratio.parent ∘ o
include hA hP hQ hc ht hr hA hD hX hE hm
include hR hT hL hv hJ hG hV hy hz hl hk hw hh
-- prices to B. Any payroll. Organizing coolant when Reader alphabet specified independently.
lemma supply (hp':(∑ i:V,w i*t₁ i) + y*(∑ i:V,2*w i*(ξ₁ i+y₁ i)) + t₀≤ σ):∃ (N:Type)(_:Fintype N)(M:N→ Menu.Hat B P)(φ:N→ Config G n→ℝ)(g:V→Response G n')(C':N→Prop), (∀ i,(M i).s.val.image o⊆ (M i).M.crest)∧ (∀ i,C' i→ Fan.ProductInk (M i).M (φ i) k j l∧∀ j,(M i).M.turn=.logKey j→ (P.activities.reg j).support⊆ Animals.neighbors l (P.activities.reg j).site)∧ Accent.Garnish P'.p o' g w (P'.p.supportExponent+1) z ∧ (∀ i j U,(∑ a,owl (M a) L j i U)+hook P'.activities P'.p.threshold (g j) i U=C j i U) ∧ (∀ U,(Accent.restore P F G0 H K U)=Poly.pass (Mach B v)*Expense M w T U)∧ XPre.banks M C' y w≤ σ+(Real.exp σ-1):=by
    have he:= hP.pure
    obtain ⟨Z,hZ,Q,N,hN,hN',p,q,M₁,hM,hI,hF,hX',hcA,hcB⟩:= XPre.rallyV B F G0 C v w he L o o' t₁ q₁ ξ₁ hv hT hL y₁ hw
    obtain ⟨Jv,A',W,f,C₃,hO,hS,hS₁,hcP,hGx,hKx⟩:= Sail.tendered B I A D H K hr hc ht w hA hD hP hQ hX hE hm hy
    let Y₁:=Sum.elim p q; let Y₀:= Sum.elim Y₁ W; let C0:Q⊕N→Prop:=fun i=>i.isLeft; let C1:= Sum.elim C0 C₃
    have hZ' i: C0 i → ∃ t, Fan.SoloInk (Y₁ i).M t k m l∧ ∀ j,(Y₁ i).M.turn=Wing.logKey j→ (P.activities.reg j).support⊆ Animals.neighbors l (P.activities.reg j).site:=by
       cases i with
       | inl i=>
          intro _
          obtain ⟨j,t,h⟩:= hM i; obtain ⟨hp₁,hj⟩:=XPre.powered h (hJ j); exact ⟨t,tall_ink hp₁ (hG j),hj⟩
       | inr i=> exact fun h=> False.elim (Bool.noConfusion h)
    choose! g hg₁ hg₂ using hZ'
    have hr(i):(Y₀ i).s.val.image (o)⊆ (Y₀ i).M.crest:=by cases i;exact M₁ _; exact hO _
    let φ:= Sum.elim g f; refine ⟨Mound Y₀,inferInstance,heap Y₀,XPre.expoH Y₀ φ,Z,XPre.alphaH Y₀ C1,?_,fun i=>XPre.pres Y₀ C1 φ ?_ hl hk hh hV i, ?_,?_,?_,?_⟩
    · rintro (i|i); exact hr _; exact Menu.fills Y₀ _ i.2.val o hr
    · rintro (i|i) hi; exact ⟨hg₁ i hi,hg₂ i hi⟩; exact hS₁ i hi
    · refine ⟨fun i j=> (hZ i).shaped _,fun i j=> (hZ i).marked _,fun i=>?_ ⟩
      obtain ⟨c,hC,hE⟩:= (hZ i).toll; refine ⟨c,hE,le_trans ?_ (hz i)⟩
      apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap hC Finset.univ) (he i).le); rw [Finset.mul_sum]; refine Finset.sum_le_sum fun l _=>?_ ; unfold Local.reservedMass; rw [mul_left_comm,show P'.p.supportExponent+1+1=P'.p.supportExponent+2 by ring]
    · intro i j U; rw [freeze,Fintype.sum_sum_type,show (∑ l:Q⊕N,owl (Y₀ (Sum.inl l)) L j i U) = _ from hX' i j U];rw [Finset.sum_eq_zero (s:=Finset.univ (α:=Jv)),add_zero,sub_add_cancel]; intro k _; refine if_neg ?_; intro h; have hx:= hS k; rw [show (W k).s=B.fire j from h] at hx; simp [Census.fire] at hx
    · apply XPre.coast B Y₀ F G0 v w he H K (Accent.restore P F G0 H K) rfl _ _ hR
      · intro U; rw [Port.grouped, hGx]; rw [hI U] -- maybe fails
      intro i U; rw [Port.registered,hKx,hF i U]
    apply XPre.fas Y₀ C1 y w he hy; apply le_trans _ hp'; unfold XPre.banks; rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; apply add_le_add _ hcP; simp only [C1,C0,Sum.elim_inl,Sum.isLeft_inl, Sum.isLeft_inr, ↓reduceIte, Bool.false_eq_true,one_mul]; rw [← Finset.mul_sum]; exact add_le_add hcA (mul_le_mul_of_nonneg_left hcB (zero_le_one.trans hy))
end YM.LocalLTE.Sail
