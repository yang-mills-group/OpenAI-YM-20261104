import YM.Integration.WilsonAddressedPublicOpticalClock
import YM.Integration.WilsonAddressedPublicOpticalPair

/-! Physical width of a reflected source at its own scale, uniformly over the elected cards. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
namespace YM.Integration.WilsonAddressedPublicHomeWidth
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

theorem pooled (simple:G.Simple)(bliss:Bliss F l z H)(T:ℕ):
    ∀ᶠ r in trail,∀{D:ℕ}(B:Book F (l:=l) H z D T r)(d:Fin (D+1))(v:S.Field d.val),
    let m:=width F B d v false
    0 < m ∧ m ≤ B.stock.j ∧ mesh m ≤ r:=by
  obtain ⟨C,_,budget⟩:=invoice F simple bliss T
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have small:Tendsto (fun s=>C*(wilson z s)^4) trail (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=C)).mul ((link.conforms simple).pow 4)
  filter_upwards [budget,small.eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin,
    (gt_mem_nhds (R.family.S.a_pos 0)).filter_mono nhdsWithin_le_nhds] with r fee fit rp short D B d v m
  let slot:=(B.stock.department d.val (Nat.le_of_lt_succ d.isLt)).print v
  have money:mesh m≤r:=calc
    _ ≤ radius z T r*dock (radius z T r)^T:=slot.front.le
    _ = r*((dock (radius z T r)^T*(wilson z r)^(2*T))*(wilson z r)^4):=by rw [radius,pow_add];ring
    _ ≤ r*(C*(wilson z r)^4):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right fee.2 (by positivity)) rp.le
    _ ≤ r:=mul_le_of_le_one_right rp.le fit
  have live:0 < m:=by
    by_contra! absent
    have := Nat.eq_zero_of_le_zero absent
    rw [this] at money
    exact (not_le_of_gt short) money
  exact ⟨live,slot.fore.trans_eq ((B.stock.department d.val _).dated v).1,money⟩

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(cash:PostT (A))(slow:WilsonWindowReportingPace.Slow R.kit)
    (T:ℕ){p:ℝ}(pp:0<p):
    ∃M₀:ℝ,1≤M₀ ∧ ∀ᶠ r in trail,∀{D:ℕ}(B:Book F (l:=l) H z D T r),Housed F B →
    ∀(d:Fin (D+1))(v:S.Field d.val)(b:Bool),let m:=width F B d v b
    0 < m ∧ mesh (m-1)*((wilson z r)^2)^p ≤ r*M₀:=by
  obtain ⟨floor,blocks⟩:=eventually_atTop.mp (block_upper (A) simple cash)
  obtain ⟨M₀,mp,rate⟩:=WilsonAddressedPublicOpticalClock.original F simple bliss slow T floor pp
  refine ⟨M₀,mp,?_⟩
  filter_upwards [rate,pooled F simple bliss T,self_mem_nhdsWithin] with r budget printed rp D B house d v b m
  have h:=budget B
  let j:=berth R 5 (max B.stock.j B.W.k)
  let g:=((wilson z r)^2)^p
  have gp:0 ≤ g:=Real.rpow_nonneg (sq_nonneg _) _
  cases e:b with
  | false=>
    have dated:=printed B d v
    have pos:0 < m:=by simpa only [m,e] using dated.1
    have enrolled:m≤j:=by simpa only [m,e] using dated.2.1.trans h.2.1
    have own:mesh m≤r:=by simpa only [m,e] using dated.2.2
    have paid:mesh (m-1)≤ν j*mesh m:=(WilsonAddressedPublicOpticalPair.previous (R:=R) cash pos enrolled (blocks j h.1)).2
    have big:1 ≤ ν j:=Real.one_le_exp (sq_nonneg _)
    have roof:(ν j)*g ≤ M₀:=(mul_le_mul_of_nonneg_right (le_self_pow₀ big (by decide:6≠0)) gp).trans (h.2.2.2 (i:=j) le_rfl)
    refine ⟨pos,?_⟩
    calc
      _ ≤ ((ν j)*r)*g:=mul_le_mul_of_nonneg_right (paid.trans (mul_le_mul_of_nonneg_left own (zero_le_one.trans big))) gp
      _ = r*((ν j)*g):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left roof rp.le
  | true=>
    have mm:m=purchaseWidth B.W:=by simp [m,e,WilsonAddressedPublicSelfCards.width]
    have pos:0 < m:=mm.symm ▸ house.2.1
    have enrolled:m≤B.W.k:=by
      rw [mm]
      exact (gain_under ..).trans (gain_under ..)
    have paid:mesh (m-1)≤(ν B.W.k)*mesh m:=(WilsonAddressedPublicOpticalPair.previous (R:=R) cash pos enrolled house.2.2.2.2.2).2
    have own:mesh m≤r*(ν B.W.k)^5:=mm.symm ▸ house.2.2.2.2.1
    have positive:0≤ν B.W.k:=(Real.exp_pos _).le
    refine ⟨pos,?_⟩
    calc
      _ ≤ ((ν B.W.k)*(r*(ν B.W.k)^5))*g:=mul_le_mul_of_nonneg_right (paid.trans (mul_le_mul_of_nonneg_left own positive)) gp
      _ = r*((ν B.W.k)^6*g):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left (h.2.2.2 h.2.2.1) rp.le

end YM.Integration.WilsonAddressedPublicHomeWidth
end
