import YM.Integration.WilsonOriginalTwoFlatGridWindow
import YM.Integration.WilsonWindowReportingPace

/-! The capture date is chosen from the physical covering radius, before
the ultraviolet cutoff, the period, the source and the flat receiver. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatGridRadius
open Function Filter Set Lattice RG Source Labels Wilson OPE Next.Rank Overlay Bid
open MergeProof Ribbons Accent ManyCopies Cells Extra.Histories RG16 RG16.Literal
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Set Function Filter MeasureTheory
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "β" => (P).clock.hatBeta
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale

private theorem crossing {t:ℝ}(tp:0<t) : ∃j:ℕ,a (j+2)<t:=by
  have h:=((C).S.shrinks.eventually (gt_mem_nhds tp)).exists
  obtain ⟨j,hj⟩:=h
  exact ⟨j,((C).S.strictAnti.antitone (by omega: j≤j+2)).trans_lt hj⟩

def date (t:ℝ)(tp:0<t):ℕ:=Nat.find (crossing R tp)

theorem covers {u:ℕ}{t:ℝ}(tp:0<t)(small:t≤a (u+3)):
    let c:=date R t tp
    u≤c ∧ a (c+2)<t ∧ t≤a (c+1):=by
  let c:=date R t tp
  have hc:a (c+2)<t:=Nat.find_spec (crossing R tp)
  have before:=((C).S.strictAnti.lt_iff_gt.mp (hc.trans_le small))
  have prev:=Nat.find_min (crossing R tp) (show c-1<c by omega)
  have move:c-1+2=c+1:=by omega
  rw [move] at prev
  exact ⟨by omega,hc,le_of_not_gt prev⟩

include simple in
private theorem blockSmall (slow:WilsonWindowReportingPace.Slow R.kit) {i j:ℕ} (early:i≤j):
    (((C).S.block i).val:ℝ) ≤ β j:=by
  have bound:=slow.2 i
  have monotone:=RG16.Literal.lambda_mono C simple |>.monotone early
  have lp:=RG16.Literal.lambda_pos C j
  have bw:=Real.log_le_sub_one_of_pos lp
  have bh:=Real.log_le_sub_one_of_pos ((P).fits.delayed j |>.trans' zero_lt_one)
  calc
    (((C).S.block i).val:ℝ) ≤ Real.log (RG16.Lambda P i):=bound
    _ ≤ Real.log (RG16.Lambda P j):=Real.log_le_log (RG16.Literal.lambda_pos C i) monotone
    _ ≤ β j := by unfold RG16.Lambda at *;linarith

include simple in
theorem fitted (slow:WilsonWindowReportingPace.Slow R.kit) {u j B:ℕ}{t:ℝ}(tp:0<t)
    (small:t≤a (u+3))(fine:a j<t)(span:t≤(β j)^B*a j) :
    let c:=date R t tp
    u≤c ∧ c+1<j ∧ t≤a (c+1) ∧ a c≤(β j)^(B+2)*a j:=by
  let c:=date R t tp
  obtain ⟨uc,hit,cover⟩:=covers R tp small
  have before:=((C).S.strictAnti.lt_iff_gt.mp (lt_of_lt_of_le fine cover))
  have p₀:=blockSmall R simple slow (show c≤j by change date R t tp+1<j at before;dsimp [c];omega)
  have p₁:=blockSmall R simple slow (show c+1≤j from before.le)
  have first: a c = ((C).S.block c).val*a (c+1):=by rw [(C).S.a_step];field_simp
  have next: a (c+1) = ((C).S.block (c+1)).val*a (c+2):=by
    rw [show c+2=c+1+1 by omega, (C).S.a_step (c+1)];field_simp
  have βpos:0 ≤ β j:=((P).fits.delayed j).le.trans' zero_le_one
  have blockPos (i:ℕ):0 ≤ (((C).S.block i).val:ℝ):=by positivity
  refine ⟨uc,before,cover,?_⟩
  calc
    a c=(((C).S.block c).val:ℝ)*(((C).S.block (c+1)).val*a (c+2)):= by rw [first];conv_lhs=>rw [next]
    _ ≤ β j*(β j*t) := mul_le_mul p₀ (mul_le_mul p₁ hit.le ((C).S.a_pos _).le
      ((P).fits.delayed _ |>.le.trans' zero_le_one)) (mul_nonneg (blockPos _) ((C).S.a_pos _).le) βpos
    _ ≤ β j*(β j*((β j)^B*a j)) := by gcongr
    _ = (β j)^(B+2)*a j:=by ring

variable {r W pupil}(L:Package R.family W r pupil)
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I](d:I→ℕ)
open WilsonOriginalTwoFlatGridCapture (word)
include simple L in
theorem original (slow:WilsonWindowReportingPace.Slow R.kit) {J u:ℕ}(stop:Stop C 0 J u)
    (D B q:ℕ) : ∀ᶠ j:ℕ in atTop,∀{t:ℝ},0<t → t≤a (u+3) → a j<t → t≤(β j)^B*a j →
    ∀N p:ℕ,∀hN:j<N,∀o:I → Cover,(∀i,8*‖(C).S.gridPoint j (o i)‖≤t) →
    (Pairwise fun i i'=>2*a j*(((P).budget j).B:ℝ)^2 ≤
        ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
    ∀Y:∀i,(C).label (d i),(∀i,Spindle.paid C (d i) j N p (Y i) ≤ (β j)^D) →
    let F:=word R d j N p hN.le o Y
    ∀uj:u≤j,‖(C).omega N p F-WilsonThermometerUnitFilingCoarse.reading R (N:=N)
      (credit C N p 0 F u (uj.trans hN.le)) u le_rfl‖ ≤ ((β j)^q)⁻¹:=by
  filter_upwards [WilsonOriginalTwoFlatGridWindow.original R simple d L stop D (B+2) q] with j paid
  intro t tp small fine span N p hN o enter apart Y budget
  dsimp only
  intro uj
  let c:=date R t tp
  obtain ⟨uc,cj,house,cost⟩:=fitted R simple slow tp small fine span
  have heard:=paid c (by omega) cost uc cj N p hN o (fun i=>(enter i).trans house) apart Y budget
  let F:=word R d j N p hN.le o Y
  have cont:Continuous F:= continuous_finsetProd _ fun i _=>(C).continuousO N p (d i) (Y i) _
  dsimp only at heard
  unfold WilsonThermometerUnitFilingCoarse.reading at heard ⊢
  rw [WilsonThermometerUnitFilingCoarse.cutoff R (by omega : c≤N) uc F cont] at heard
  rw [gust_base]
  exact heard

end YM.Integration.WilsonOriginalTwoFlatGridRadius
end
