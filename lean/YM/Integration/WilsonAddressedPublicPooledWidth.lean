import YM.Integration.WilsonAddressedPublicHomeWidth

/-! On the pooled arm the full previous cell already fits at the physical scale. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
namespace YM.Integration.WilsonAddressedPublicPooledWidth
open Set Finset Filter Function Lattice Wilson RG Source Labels Cells OPE
open PhysicalNext.Repeat.Legato Extraction Spec Table Climb GapsContact GapsContact.Seams
open GapsContact.Stamps Trace.Pilot Trace.Terrace Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open WilsonInvariantActionPosition WilsonReflectedOriginalPrefixTariff WilsonOriginalTwoFlatPublicBooks
open WilsonAddressedPublicSelfCards (width)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonThermometerUnitFilingFourPoolClock (invoice)
open WilsonThermometerUnitFilingFourPoolShell (radius)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Arch R.family}
local notation "A" => R.family.path.levels
local notation "mesh" => R.family.S.a
local notation "ν" => (A).clock.monitor


theorem original (simple:G.Simple)(bliss:Bliss F l z H)(cash:PostT (A))(slow:WilsonWindowReportingPace.Slow R.kit)
    (T:ℕ):∃C₀:ℝ,1≤C₀ ∧ ∀ᶠ r in trail,∀{D:ℕ}(B:Book F (l:=l) H z D T r)
    (d:Fin (D+1))(v:S.Field d.val),let m:=width F B d v false
    0 < m ∧ mesh (m-1) ≤ C₀*r*(wilson z r)^2:=by
  obtain ⟨C,cp,invoiced⟩:=invoice F simple bliss T
  obtain ⟨floor,blocks⟩:=eventually_atTop.mp (block_upper (A) simple cash)
  obtain ⟨M,mp,clock⟩:=WilsonAddressedPublicOpticalClock.original F simple bliss slow T floor (η:=1) one_pos
  refine ⟨M*C,one_le_mul_of_one_le_of_one_le mp cp,?_⟩
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  filter_upwards [invoiced,clock,WilsonAddressedPublicHomeWidth.pooled F simple bliss T,
    self_mem_nhdsWithin,link.positive] with r fee budgets actual rp gp D B d v m
  let slot:=(B.stock.department d.val (Nat.le_of_lt_succ d.isLt)).print v
  have measured:=actual B d v
  let j:=berth R 5 (max B.stock.j B.W.k)
  have bought:=budgets B
  have dated:m≤j:=measured.2.1.trans bought.2.1
  have first:mesh (m-1)≤ν j*mesh m:=(WilsonAddressedPublicOpticalPair.previous (R:=R) cash measured.1 dated (blocks j bought.1)).2
  let g:=wilson z r
  have units:mesh m≤r*(C*g^4):=calc
    _ ≤ radius z T r*dock (radius z T r)^T:=slot.front.le
    _ = r*((dock (radius z T r)^T*g^(2*T))*g^4):=by dsimp only [g];rw [radius,pow_add];ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right fee.2 (by positivity)) rp.le
  have pos:1≤ν j:=Real.one_le_exp (sq_nonneg _)
  have meter:ν j*g^2 ≤ M:=by
    have roof:=(mul_le_mul_of_nonneg_right (le_self_pow₀ pos (by decide:6≠0)) (sq_nonneg g)).trans
      (show (ν j)^6*g^2≤M by simpa only [Real.rpow_one] using bought.2.2.2 (le_refl j))
    exact roof
  refine ⟨measured.1,first.trans ((mul_le_mul_of_nonneg_left units (zero_le_one.trans pos)).trans ?_)⟩
  calc
    (ν j)*(r*(C*g^4))=((ν j)*g^2)*(C*r*g^2):=by ring
    _ ≤ M*(C*r*g^2):=mul_le_mul_of_nonneg_right meter (mul_nonneg ((mul_nonneg (zero_le_one.trans cp) rp.le)) (sq_nonneg _))
    _ = _:=by ring

end YM.Integration.WilsonAddressedPublicPooledWidth
end
