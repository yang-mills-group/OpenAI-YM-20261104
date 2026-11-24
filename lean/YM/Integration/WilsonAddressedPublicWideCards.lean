import YM.Integration.WilsonAddressedPublicPairFence
import YM.Integration.WilsonAddressedPublicCardCapacity
import YM.Integration.WilsonOriginalPublicRelativeGramWideStation

/-! The genuine reporting fields and their original matrix salary at the wide reflection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option quotPrecheck false
namespace YM.Integration.WilsonAddressedPublicWideCards
open Set Filter Finset Function Lattice Wilson RG Source Labels Cells OPE
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical Trace.Pilot PhysMS
open FVA2 FVA2.Register Climb GapsContact Next.Rank
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonOriginalPublicRelativeGramPins (cutoff)
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits)
open WilsonOriginalPublicRelativeGramTransport (transition)
open WilsonOriginalPublicRelativeGramAddresses (ports)
open WilsonOriginalPublicRelativeGramWideStation (Receives)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicPairPins (name cost whenFiled)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicHomeCard (exponent)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S)(Z:WilsonPrescription G){l:Ultrafilter (ℕ×ℕ)}
    {z:Trace.Terrace.Arch R.family}{H:(Bel R.family.book).Hierarchy}
    (β:Local.Physical.Deck G)(h:ℕ)
local notation "I" => Glyph β h
local notation "C" => R.family
local notation "P" => named R β h

def filed (r s:ℝ)(b:Bool)(i:I):S.Field h:=J (cond b s r) h (P i)

variable {D T:ℕ}(d:h≤D){r s:ℝ}(br:Bool→I→Bool)
local notation "degree" => (⟨h,Nat.lt_succ_of_le d⟩:Fin (D+1))
local notation "vec" => filed R J β h r s

variable (book:∀b,Book F (l:=l) H z D T (cond b s r))
def wage {D T:ℕ}{r s:ℝ}(hcap:h≤D)(books:∀n,Book F (l:=l) H z D T (cond n s r))
    (choose:Bool→(Glyph β h)→Bool)(i j:Glyph β h):ℝ:=
  cost R F books ⟨h,Nat.lt_succ_of_le hcap⟩ (filed R J β h r s) choose false i*
    cost R F books ⟨h,Nat.lt_succ_of_le hcap⟩ (filed R J β h r s) choose true j

include Z in
theorem price (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F J)(T:ℕ):
    ∃A δ:ℝ,0≤A ∧ 0<δ ∧ ∀r s:ℝ,r∈Ioc (0:ℝ) δ → s∈Ioc (0:ℝ) δ →
    ∀{D:ℕ}(d:h≤D)(book:∀b,Book F (l:=l) H z D T (cond b s r)),
    (∀b,Housed F (book b)) → ∀br:Bool→I→Bool,∀i j,
    wage R F J β h d book br i j*((wilson z r)^(exponent T h)*(wilson z s)^(exponent T h)) ≤
      (A*‖P i‖)*(A*‖P j‖):=by
  obtain ⟨A,ap,res⟩:=WilsonAddressedPublicCardCapacity.original F J Z simple bliss lead T h
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨δ,dp,all⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp (res.and (link.positive.and ((link.conforms simple).eventually (ge_mem_nhds zero_lt_one) |>.and ((ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds))))
  refine ⟨A,δ,ap,dp,?_⟩
  intro r s rp sp D d book housed br i j
  let rank:Fin (D+1):=⟨h,Nat.lt_succ_of_le d⟩
  let side:=fun b:Bool=>cond b s r
  have bound(b:Bool)(n:I):cost R F book rank (filed R J β h r s) br b n*
      (wilson z (side b))^(exponent T h) ≤ A*‖P n‖:=by
    have atHome:side b∈Ioc (0:ℝ) δ:=by cases b <;> assumption
    have h₀:=(all atHome).1 d (book b) (housed b) (filed R J β h r s b n) (br b n)
    simpa only [side,filed,cost,LinearEquiv.symm_apply_apply] using h₀
  have positive(b:Bool)(n:I):0 ≤ cost R F book rank (filed R J β h r s) br b n:=by
    have atHome:side b∈Ioc (0:ℝ) δ:=by cases b <;> assumption
    have row:=(all atHome).2
    have logPay {x:ℝ}(pos:0<x)(one:x≤1):0≤GapsContact.Seams.dock x:=by
      unfold GapsContact.Seams.dock Trace.Pilot.LogV
      rw [Real.log_inv]
      linarith [Real.log_nonpos pos.le one]
    cases flag:br b n
    · change 0 ≤ WilsonAddressedPublicSelfCards.fee F (book b) rank (filed R J β h r s b n) (br b n)
      rw [flag]
      apply mul_nonneg _ (GapsContact.Ascent.cost_pos ..)
      refine pow_nonneg (logPay ?_ ?_) _
      · exact mul_pos atHome.1 (pow_pos row.1 _)
      · exact (mul_le_of_le_one_right atHome.1.le (pow_le_one₀ row.1.le row.2.1)).trans row.2.2
    · change 0 ≤ WilsonAddressedPublicSelfCards.fee F (book b) rank (filed R J β h r s b n) (br b n)
      rw [flag]
      exact mul_nonneg (logPay atHome.1 row.2.2) (norm_nonneg _)
  change (_*_)*(_*_) ≤ _
  rw [mul_mul_mul_comm]
  exact mul_le_mul (bound false i) (bound true j)
    (mul_nonneg (positive true j) (pow_nonneg (all sp).2.1.le _)) (mul_nonneg ap (norm_nonneg _))

theorem original (d:h≤D)(book:∀b,Book F (l:=l) H z D T (cond b s r)) (branches:Bool→(Glyph β h)→Bool)(a:Axis)(avoid:Finset E4)(site:ℕ)(t K:ℝ)(cash:Trace.Terrace.PostT (C).path.levels)
    (office:Receives (f:=f) (S:=S) β h a R J l site t r K avoid)
    (compact:‖(C).S.gridPoint site (ports R avoid (pointsAt a) site t 0-ports R avoid (pointsAt a) site t 1)‖≤1)
    (geometry:∀i j:I,
      let m:=min (whenFiled R F book (⟨h,Nat.lt_succ_of_le d⟩:Fin (D+1)) (filed R J β h r s) branches false i) (whenFiled R F book (⟨h,Nat.lt_succ_of_le d⟩:Fin (D+1)) (filed R J β h r s) branches true j)
      0 < m ∧ 2*(C).S.a (m-1) < ‖(C).S.gridPoint site (ports R avoid (pointsAt a) site t 0)-
        (C).S.gridPoint site (ports R avoid (pointsAt a) site t 1)‖):
    let Y:=name R F book (⟨h,Nat.lt_succ_of_le d⟩:Fin (D+1)) (filed R J β h r s) branches
    let expenses:=wage R F J β h d book branches
    let ω:=fun _:Unit=>ports R avoid (pointsAt a) site t
    let μ:=fun _:Unit=>(1:ℂ)
    ∀(W:Initialize G)(sale:Dated (L:=Unit) R W (fun _:I=>h))(σ old:Bool→I→I→ℝ)(η accuracy:ℝ),
    (∀ᶠ z:ℕ×ℕ in f.fuse,∀b i j,‖cutoff R a (fun _:I=>h) site ω μ Y b z i j-
      submitted R W (fun _:I=>h) sale b z i j‖≤σ b i j ∧ deposits R W (fun _:I=>h) sale b z i j≤old b i j) →
    0<η → K*max 0 (WilsonOriginalPublicRelativeGramJoined.fee η (σ false+old false))≤1/2 →
    2*K*(max 0 (WilsonOriginalPublicRelativeGramJoined.fee η (σ true+old true))+
      max 0 (WilsonOriginalPublicRelativeGramJoined.fee η (σ false+old false))*(K*(∑i,∑j,expenses i j)))≤accuracy →
    ‖transition R h J P r s‖≤K*(∑i,∑j,expenses i j) ∧ ∀ᶠ z:ℕ×ℕ in (l:Filter (ℕ×ℕ)),
      IsUnit (sale.frame false z).det ∧ ‖transition R h J P r s-(sale.frame false z)⁻¹*sale.frame true z‖≤accuracy:=by
  classical
  intro Y expenses ω μ W sale σ old η accuracy earned ep core full
  let arm:=fun b i=>((book b).rows (⟨h,Nat.lt_succ_of_le d⟩:Fin (D+1))).arm (branches b i) (filed R J β h r s b i)
  apply office W s Y (fun b i=>(arm b i).label) sale expenses σ old η accuracy (fun b i=>(arm b i).approaches)
    (fun b i=>(arm b i).represents) _ earned ep core full
  refine eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>?_))
  have paid:=WilsonAddressedPublicPairFence.original R F book (⟨h,Nat.lt_succ_of_le d⟩:Fin (D+1)) (filed R J β h r s) branches cash true i j site ω μ (geometry i j).1
    (fun _=>compact) (fun _=>(geometry i j).2)
  filter_upwards [paid] with u receipt
  simpa only [Y,expenses,ω,μ,wage,norm_one,Fintype.sum_unique,one_mul] using receipt a

end YM.Integration.WilsonAddressedPublicWideCards
end
