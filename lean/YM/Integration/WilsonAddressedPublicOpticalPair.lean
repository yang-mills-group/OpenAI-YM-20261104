import YM.Integration.WilsonAddressedPublicSampledCards
import YM.Integration.WilsonAddressedPublicCardBooks

/-! The genuine two original card dates in the physical optical experiment. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonAddressedPublicOpticalPair
open Filter Finset Function Lattice RG Wilson Source Labels OPE Cells Extraction Spec
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat Table Climb GapsContact GapsContact.Ascent
open Trace Trace.Terrace GapsContact.Stamps Next.Rank Next.Rank.Station
open Seams
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicSelfCards (width fee)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSampledCards (leaf)
open WilsonThermometerUnitFilingFourPoolShell (radius)
open scoped Classical BigOperators

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Arch R.family}
    {D T:ℕ}{r:Fin 2→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin 2→Fin (D+1))(v:∀i,S.Field (d i).val)(b:Fin 2→Bool)
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "widths" => (fun i=>width F (B i) (d i) (v i) (b i))
local notation "fees" => (fun i=>fee F (B i) (d i) (v i) (b i))

def length {r:ℝ}(book:Book F (l:=l) H z D T r)(br:Bool):ℝ:=
  if br then r*((A).clock.monitor book.W.k)^5 else
    (radius z T r)*dock (radius z T r)^T

theorem bounded (house:∀i,Housed F (B i))(i:Fin 2):
    (C).S.a (widths i)≤length F (B i) (b i):=by
  change (C).S.a (width F (B i) (d i) (v i) (b i)) ≤ _
  cases flag:b i with
  | false=>
    exact (((B i).stock.department (d i).val (Nat.le_of_lt_succ (d i).isLt)).print (v i)).front.le
  | true=>exact (house i).2.2.2.2.1

theorem previous (cash:PostT (A)){m k:ℕ}(live:0 < m)(later:m ≤ k){M:ℝ}
    (upper:∀i:ℕ,i ≤ k → (((C).S.block i).val:ℝ) ≤ M):
    12*((C).S.a m)<(C).S.a (m-1) ∧ (C).S.a (m-1) ≤ M*(C).S.a m:=by
  obtain ⟨t,rfl⟩:=Nat.exists_eq_succ_of_ne_zero live.ne'
  have floor:=cash.cropK t
  unfold ctl at floor
  have t₀:12<((C).S.block t).val:=by change 12<((A).S.block t).val; omega
  have pos:0<(((C).S.block t).val:ℝ):=by exact_mod_cast ((C).S.block t).property
  have step:(C).S.a t=(((C).S.block t).val:ℝ)*(C).S.a (t+1):=by
    rw [(C).S.a_step]; field_simp
  rw [Nat.succ_sub_one]
  constructor
  · rw [step]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast t₀) ((C).S.a_pos _)
  · rw [step]
    exact mul_le_mul_of_nonneg_right (upper _ (by omega)) ((C).S.a_pos _).le

theorem original (cash:PostT (A))(simple:G.Simple)(house:∀i,Housed F (B i)):
    ∃first:ℕ,∀k:ℕ,first ≤ k → (∀i,widths i ≤ k) →
    let m:=min (widths 0) (widths 1)
    let wall:=max (length F (B 0) (b 0)) (length F (B 1) (b 1))
    0 < m → ∀ᶠ w:ℕ×ℕ in f.fuse,
    ∀(L:Type)[Fintype L](u:L→Fin 2→Site ((C).side w.1 w.2))(μ:L→ℂ)
      (conj:L→Fin 2→Bool)(motion:L→Fin 2→Signed), (∀a i,Push.RelayDifference.diag (motion a i)) →
    (∀a i i',i≠i' → (A).clock.monitor k*wall < (C).S.a w.1*(separation (u a i) (u a i'):ℝ)) →
    ‖∑a,μ a*moment ((C).beta w.1 w.2) (fun U=>∏i,Push.RelayDifference.oriented
      (leaf F B d v b w i) (conj a i) (motion a i) (u a i) U)‖ ≤
    (∑a,‖μ a‖)*∏i,fees i:=by
  classical
  obtain ⟨J,start⟩:=eventually_atTop.1 (block_upper (A) simple cash)
  refine ⟨J,?_⟩
  intro k jk top m wall mp
  have low(i:Fin 2):m ≤ widths i:=by fin_cases i <;> first | exact min_le_left .. | exact min_le_right ..
  have ceiling:(C).S.a m ≤ wall:=by
    rcases le_total (widths 0) (widths 1) with h|h
    · change (C).S.a (min _ _) ≤ max _ _;rw [min_eq_left h]
      exact (bounded F B d v b house 0).trans (le_max_left ..)
    · change (C).S.a (min _ _) ≤ max _ _;rw [min_eq_right h]
      exact (bounded F B d v b house 1).trans (le_max_right ..)
  have room:=previous (R:=R) cash mp ((low 0).trans (top 0)) (start k jk)
  have clock:0≤(A).clock.monitor k:= (Real.exp_pos _).le
  have clear:=room.2.trans (mul_le_mul_of_nonneg_left ceiling clock)
  have live:∀ᶠ w:ℕ×ℕ in f.fuse,m ≤ w.1:=by
    rw [Extraction.Order.fused]
    unfold Extraction.Order.late
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop m
  filter_upwards [WilsonAddressedPublicSampledCards.original F B d v b,live] with w receipt hw
  intro L _ u μ conj motion diag sep
  apply receipt (m-1) m (by omega) hw low _ L u μ conj motion diag
  · exact fun a i i' h=>clear.trans_lt (sep a i i' h)
  · norm_num; linarith [room.1]

end YM.Integration.WilsonAddressedPublicOpticalPair
end
