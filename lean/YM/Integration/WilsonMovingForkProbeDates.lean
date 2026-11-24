import YM.Integration.WilsonMovingForkLocalReceipt

/-! The filed master on the near clock and the spectator's own clock at
the actual aperture used by the positive quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkProbeDates
open RG Wilson Source Maxwell Maxwell.Free RG05Readout Climb GapsContact.Seams
open Function Filter Set Lattice Extraction Table Spec PhysMS Trace Trace.Pilot
open GapsContact GapsContact.Ascent OPE RG16 RG16.Literal RG17 FVA2 FVA2.Register MS MS.Land
open PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonMovingForkProbeMaster WilsonMovingForkLocalReceipt
open WilsonMovingForkPositionIntegrals (nearTags twoTags)
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
  (J:ℝ→tower S)(Z:WilsonPrescription G){n h:ℕ}{P:Type}

def dates {δ:ℝ}(r t:{x:ℝ //0<x ∧ x<δ})(i:Seat G n h P):{x:ℝ //0<x ∧ x<δ}:=
  match i with
  | some (.inr (.inr _))=>t
  | _=>r

theorem file_dates {δ:ℝ}(r t:{x:ℝ //0<x ∧ x<δ}):
    (∀i:Seat G n h P,(dates r t i).val=home r.val t.val i) ∧
    (∃i:Seat G n h P,(dates r t i).val=r.val) ∧
    (r.val≤t.val → ∀i:Seat G n h P,r.val≤(dates r t i).val ∧ (dates r t i).val≤t.val):=by
  have cases_(i:Seat G n h P):dates r t i=r ∨ dates r t i=t:=by
    rcases i with _|i;exact Or.inl rfl
    rcases i with _|i;exact Or.inl rfl
    cases i <;> first|exact Or.inl rfl|exact Or.inr rfl
  refine ⟨?_,⟨none,rfl⟩,?_⟩
  · rintro (_|(_|(_|_))) <;> rfl
  · intro rt i
    rcases cases_ i with e|e <;> rw [e] <;> exact ⟨by first|rfl|exact rt,by first|rfl|exact rt⟩

theorem whole {δ:ℝ}(r t:{x:ℝ //0<x ∧ x<δ})(d:Fin n→ℕ)
    (v:∀i,Free R.family (d i))(a:P→Free R.family h)(p:P):
    physical F J Z (bound (P:=P) d) (dose d v a) (dates r t) (WilsonMovingForkProbeMaster.whole p)=
      nearTags F J d h Z (r:=r.val) (t:=t.val) v (a p):=by
  rw [← WilsonMovingForkProbeMaster.whole_uses F J Z d v a r.val t.val p]
  funext i
  dsimp [physical,axis]
  rw [(file_dates r t).1]
  rfl

theorem gram {δ:ℝ}(r t:{x:ℝ //0<x ∧ x<δ})(d:Fin n→ℕ)
    (v:∀i,Free R.family (d i))(a:P→Free R.family h)(k:Dframe.Toon G h)(p:P):
    physical F J Z (bound (P:=P) d) (dose d v a) (dates r t) (pair k p)=
      twoTags F J h Z r.val t.val (a p) k:=by
  rw [← WilsonMovingForkProbeMaster.gram_uses F J Z d v a r.val t.val k p]
  funext i
  dsimp [physical,axis]
  rw [(file_dates r t).1]
  rfl

theorem aperture (simple:G.Simple)(bliss:Bliss F l z H)(A:ℕ){δ:ℝ}(dp:0<δ):
    ∀ᶠr in trail,0<r ∧ let t:=r/((wilson z r)^A)^2
      r≤t ∧ t<δ ∧ t=outer z (2*A) r:=by
  let law:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have short:∀ᶠr in trail,outer z (2*A) r<δ:=(longer F simple bliss (2*A)).eventually
    ((gt_mem_nhds dp).filter_mono nhdsWithin_le_nhds)
  filter_upwards [short,law.positive,(law.conforms simple).eventually (ge_mem_nhds zero_lt_one),length_rate.pos]
    with r small gp one rp
  have eq:r/((wilson z r)^A)^2=outer z (2*A) r:=by
    rw [outer,Nat.mul_comm 2 A,pow_mul,inv_pow,inv_pow,div_eq_mul_inv]
  have sp:0<((wilson z r)^A)^2:=by positivity
  have low:((wilson z r)^A)^2≤1:=pow_le_one₀ (pow_nonneg gp.le _) (pow_le_one₀ gp.le one)
  exact ⟨rp,(le_div_iff₀ sp).mpr (by simpa using mul_le_mul_of_nonneg_left low rp.le),by rwa [eq],eq⟩

end YM.Integration.WilsonMovingForkProbeDates
