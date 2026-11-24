import YM.Integration.WilsonThermometerUnitFilingWeakSurvey

/-! One before-length aperture for all adjacent stages and a finite floor for repetitions of the charged row. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakRoom
open Finset Lattice Laurent Bloch Metric Exterior Precision RG Next.Free Work.F08
open FormalBulk08 Flat WilsonThermometerUnitFilingWeakSurvey WilsonThermometerUnitFilingWeakKernel
open scoped Classical BigOperators

structure Pair (G:Gauge)(K:KernelChoices)(j t:ℕ) where
  width : ℝ
  cost : ℝ
  width_pos : 0<width
  cost_pos : 0<cost
  serves : 4≤j→4≤t→Staff G K j t width cost

def book (G:Gauge)(K:KernelChoices)(j t:ℕ):Pair G K j t:=
  (show Nonempty (Pair G K j t) from by
    by_cases h:4≤j ∧ 4≤t
    · obtain ⟨σ,b,hσ,hb,p⟩:=WilsonThermometerUnitFilingWeakSurvey.original G K h.1 h.2
      exact ⟨⟨σ,b,hσ,hb,fun _ _=>p⟩⟩
    · exact ⟨⟨1,1,zero_lt_one,zero_lt_one,fun a b=>(h ⟨a,b⟩).elim⟩⟩).some

abbrev Steps (x:ℕ):=Fin (x+2)×Fin (x+2)
def width (G:Gauge)(K:KernelChoices)(x:ℕ):ℝ:=
  (1+∑i:Steps x,(book G K i.1 i.2).width⁻¹)⁻¹

def ceiling (G:Gauge)(K:KernelChoices)(x:ℕ):ℝ:=
  1+∑i:Steps x,(book G K i.1 i.2).cost

theorem width_pos (G:Gauge)(K:KernelChoices)(x:ℕ):0<width G K x:=by
  unfold width
  have h:0≤∑i:Steps x,(book G K i.1 i.2).width⁻¹:=sum_nonneg fun i _=>(inv_pos.mpr (book G K i.1 i.2).width_pos).le
  exact inv_pos.mpr (by linarith)

theorem issued (G:Gauge)(K:KernelChoices)(x j t:ℕ)(hj:j≤x+1)(ht:t≤x+1):
    width G K x≤(book G K j t).width ∧ (book G K j t).cost≤ceiling G K x:=by
  classical
  let i:Steps x:=(⟨j,by omega⟩,⟨t,by omega⟩)
  have h: (book G K i.1 i.2).width⁻¹ ≤ ∑z:Steps x,(book G K z.1 z.2).width⁻¹:=
    single_le_sum (fun z _=>(inv_pos.mpr (book G K z.1 z.2).width_pos).le) (mem_univ i)
  have hb: (book G K i.1 i.2).cost ≤ ∑z:Steps x,(book G K z.1 z.2).cost:=
    single_le_sum (fun z _=>(book G K z.1 z.2).cost_pos.le) (mem_univ i)
  constructor
  · unfold width
    have π:(book G K i.1 i.2).width⁻¹≤1+∑z:Steps x,(book G K z.1 z.2).width⁻¹:=by linarith
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (book G K i.1 i.2).width_pos) π
  · change (book G K i.1 i.2).cost ≤ 1+∑z:Steps x,(book G K z.1 z.2).cost
    linarith

def groups : ℝ := max (Fintype.card (TypeFace 1):ℝ) (Fintype.card (TypeFace 2):ℝ)

def floor (G:Gauge)(K:KernelChoices)(x:ℕ):ℕ:=
  Nat.ceil (Real.exp 8*groups*ceiling G K x)

theorem gain {m:ℝ} {L:Side} (purchase:m≤(L.val:ℝ))(d:ℕ):
    m/(L.val:ℝ)^(1+d)≤1:=by
  have hL:1≤(L.val:ℝ):=by exact_mod_cast L.2
  apply (div_le_one (pow_pos (zero_lt_one.trans_le hL) _)).mpr
  exact purchase.trans (by rw [pow_add,pow_one];nlinarith [one_le_pow₀ hL (n:=d)])

end YM.Integration.WilsonThermometerUnitFilingWeakRoom
