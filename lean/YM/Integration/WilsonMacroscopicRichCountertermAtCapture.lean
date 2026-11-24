import YM.Integration.WilsonMacroscopicRichChildRemainder
import YM.Integration.WilsonMeasuredReportingProduct

/-! Return the physically reported fixed-date counterterm to the moving capture
with its original price, uniformly in the torus and upper cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCountertermAtCapture
open Filter Lattice Wilson RG Source Labels Trace.Physical.GermGraph RG16.Literal
open MergeProof MergeProof.Ribbons
open scoped BigOperators Classical Topology
variable {G : Gauge} (C : Family G) (H : C.Makes)

theorem forward (mat : Materials C) (d : ℕ) {γ : ℝ} (pos : 0<γ) :
    ∀ᶠ u : ℕ in atTop, ∀ b, u ≤ b → ∀ N p, b ≤ N → ∀ v : C.label d,
      mCost C d N p b v ≤ Real.exp (γ*(C.S.scale b-C.S.scale u))*mCost C d N p u v := by
  filter_upwards [message_graph C d mat pos (show (0:ℝ)<1 by norm_num)] with u gates
  intro b ub
  induction b,ub using Nat.le_induction with
  | base => intro N p _ v; simp
  | succ i ui ih =>
    intro N p live v
    have L : 0<factor C i := zero_lt_one.trans (factor_positive C i)
    have step := (gates i ui p N (Nat.lt_of_succ_le live)).2.1 v
    calc
      mCost C d N p (i+1) v ≤ (factor C i)^γ*mCost C d N p i v := step
      _ ≤ (factor C i)^γ*(Real.exp (γ*(C.S.scale i-C.S.scale u))*mCost C d N p u v) :=
        mul_le_mul_of_nonneg_left (ih N p (Nat.le_of_succ_le live) v) (Real.rpow_nonneg L.le _)
      _ = _ := by
        rw [Real.rpow_def_of_pos L,←mul_assoc,←Real.exp_add,Schedule.scale_succ]
        congr 2
        unfold factor
        ring

theorem original (mat : Materials C) (d : ℕ) :
    ∀ᶠ u : ℕ in atTop, ∀ (N p b J : ℕ) (ju : J≤u) (ub : u≤b) (live : b≤N)
      (door : Opened C d u p) (_opened : Opened C d b p)
      (E e w : ℝ) (Y : Cut C N p) (z : C.label d) (q : store C d p b),
      Funds C H p N b d J u E e w Y ju ub live door z q →
      let v := topReport C N p d H u door (ub.trans live) Y
      mCost C d N p b (v-(C.factory d N p).terminal.symm z) ≤
        Real.exp (-(C.S.scale b-C.S.scale u)/16) * E ∧ mCost C d N p b v ≤ 5*E := by
  filter_upwards [forward C mat d (show (0:ℝ)<1/16 by norm_num)] with u transport
  intro N p b J ju ub live door opened E e w Y z q funds v
  let a := (C.factory d N p).terminal.symm z
  let s := C.S.scale b-C.S.scale u
  have ss : 0 ≤ s := sub_nonneg.mpr ((OPE.scale_mono C.S).monotone ub)
  have delta : mCost C d N p b (v-a) ≤ Real.exp (-s/16)*E := by
    calc
      _ ≤ Real.exp ((1/16)*s)*mCost C d N p u (v-a) := transport b ub N p live _
      _ ≤ Real.exp ((1/16)*s)*(E/Bid.gainChart C.path b u) :=
        mul_le_mul_of_nonneg_left funds.currency (Real.exp_pos _).le
      _ = (Real.exp ((1/16)*s)*Real.exp (-((1/8)*s)))*E := by
        change Real.exp ((1/16)*s)*(E/Real.exp ((1/8)*s))=_
        rw [Real.exp_neg]
        ring
      _ = _ := by rw [←Real.exp_add]; congr 2; ring
  have initial := (size_gap (C:=C) d N p b H opened live a).1
  change mCost C d N p b a ≤ 2*Next.UVStress.quota C d b N p z at initial
  have posE : 0≤E := by
    have h0 : 0≤Next.UVStress.quota C d b N p z := Work.G08.size_nonneg .. 
    linarith only [funds.capZ,h0]
  have decay : Real.exp (-s/16) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨delta,?_⟩
  have triangle : mCost C d N p b v ≤ mCost C d N p b (v-a)+mCost C d N p b a := by
    change (C.labels.level d).coeffSize (fitting d N p b H opened live v) ≤
      (C.labels.level d).coeffSize (fitting d N p b H opened live (v-a))+
      (C.labels.level d).coeffSize (fitting d N p b H opened live a)
    calc
      _ = (C.labels.level d).coeffSize (fitting d N p b H opened live ((v-a)+a)) := by rw [sub_add_cancel]
      _ ≤ _ := by rw [map_add]; exact Extra.Histories.Size.add ..
  linarith only [triangle,initial,funds.capZ,delta,mul_le_mul_of_nonneg_right decay posE]

end YM.Integration.WilsonMacroscopicRichCountertermAtCapture

