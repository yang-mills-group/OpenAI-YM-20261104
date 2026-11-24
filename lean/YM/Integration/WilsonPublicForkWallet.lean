import YM.Integration.WilsonThermometerWeakRunningRoster

/-! All the running input and exterior basis fares on the single physical
matrix ticket used by the polynomial-window spatial fork. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkWallet
open Climb Finset Filter Set Spec Table Extraction Trace Trace.Pilot Trace.Terrace
open GapsContact GapsContact.Ascent GapsContact.Seams Frontier6 OPE OPE.Log
open PhysicalNext.Repeat.Legato Next.UVStress
open WilsonThermometerWeakRunningRoster
open private clock from YM.Integration.WilsonThermometerWeakRunningCoordinates
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)

theorem coordinate {simple:G.Simple}{𝓛:Ultrafilter (ℕ×ℕ)}{arch:Arch R.family}{Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arch Y)(ledger:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    {d w:ℕ}(L:S.Field d→ₗ[ℂ]ℂ)(h:w≤d)
    (kill:∀e:ℕ,∀he:e<w,∀v:S.Field e,L (F.sector.derivatives.rise (he.le.trans h) v)=0):
    ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠr in trail,∀v:S.Field d,
      ‖L v‖≤C*dock r^m*r^w*cost F d r v:=by
  obtain ⟨p,priced⟩:=WilsonThermometerWeakRunningCoordinates.assessed F ledger L h kill
  obtain ⟨t,opened⟩:=every_pool F simple bliss d
  obtain ⟨j₀,hj⟩:=eventually_atTop.1 priced
  let C:=R.family.path.levels.clock.bar+G.slopeConstant*((t:ℝ)+1)
  have cp:0≤C:=add_nonneg R.family.path.levels.clock.bar_pos.le
    (mul_nonneg (Gauge.slopeConstant_pos (G:=G) simple).le (by positivity))
  refine ⟨C^p,p+t*w+t,pow_nonneg cp _,?_⟩
  have slope:∀ᶠr in trail,r*(dock r)^t≤R.family.S.a j₀:=(lake_line t).eventually (ge_mem_nhds (R.family.S.a_pos j₀))
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [opened,slope,small,self_mem_nhdsWithin] with r hire paid small pos
  intro v
  obtain ⟨j,m,key⟩:=hire
  have sp:R.family.S.a j≤r*dock r^t:=(R.family.S.strictAnti.antitone key.fore).trans key.front.le
  have next:j₀≤j:=R.family.S.strictAnti.le_iff_ge.mp (sp.trans paid)
  have dk:0≤dock r:=zero_le_one.trans (dock_valid r ⟨pos,small⟩)
  have aj:R.family.S.a j≤1:=by simpa using R.family.S.strictAnti.antitone (Nat.zero_le j)
  have sj:0≤R.family.S.scale j:=by change 0≤Real.log (R.family.S.a j)⁻¹; rw [Real.log_inv]; linarith [Real.log_nonpos (R.family.S.a_pos j).le aj]
  have hat:0≤R.family.path.levels.clock.hatBeta j:=add_nonneg R.family.path.levels.clock.bar_pos.le (mul_nonneg (Gauge.slopeConstant_pos (G:=G) simple).le sj)
  have β:=pow_le_pow_left₀ hat (clock F (simple:=simple) key ⟨pos,small⟩) p
  have width:=pow_le_pow_left₀ (R.family.S.a_pos j).le sp w
  have marked:= hj j next r _ m (key.budget d le_rfl) v
  calc ‖L v‖≤_:= marked
       _≤(C*dock r)^p*(r*dock r^t)^w*dock r^t*cost F d r v:=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul β width (pow_nonneg (R.family.S.a_pos j).le _) (pow_nonneg (mul_nonneg cp dk) _))
            (pow_nonneg dk _)) (Real.sqrt_nonneg _)
       _=_:=by rw [mul_pow,mul_pow,←pow_mul,pow_add,pow_add];ring


theorem original {simple:G.Simple}{𝓛:Ultrafilter (ℕ×ℕ)}{arch:Arch R.family}{Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arch Y)(ledger:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (P:Prescription F.sector.derivatives)
    (hp:Prescription.Coherent P)(d:ℕ):
    ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠr in trail,∀v:S.Field d,
      rent F P d r v≤C*dock r^m*cost F d r v:=by
  let T:=↥(bands F.sector.derivatives d)
  have entry (a:T) : ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠ r in trail,∀v:S.Field d,
      ‖P.test a.1 d v‖≤C*dock r^m*r^a.1.fst*cost F d r v:=by
    exact coordinate (simple:=simple) F bliss ledger (P.test a.1 d)
      ((full_bands ..).mp a.2) (fun e he x=>by
        rw [Prescription.affinity F.room.kernel.laws.toSymmetric F.phase.transport.injection P,
          Prescription.highVan F.room.kernel.laws.toSymmetric F.phase.transport.injection hp a.1 he])
  choose C m nonneg paid using entry
  refine ⟨∑a,C a,∑a,m a,sum_nonneg (fun i _=>nonneg i),?_⟩
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_all.mpr paid,small,self_mem_nhdsWithin] with r hr h1 h0
  intro v
  have lev:1≤dock r:=dock_valid r ⟨h0,h1⟩
  unfold rent
  rw [sum_mul,sum_mul]
  apply sum_le_sum
  intro a _
  have size:m a≤∑i,m i:=single_le_sum (fun i _=>Nat.zero_le (m i)) (mem_univ a)
  calc
    _ ≤ C a*dock r^(m a)*cost F d r v := by
      apply (div_le_iff₀ (pow_pos h0 a.1.fst)).mpr
      simpa only [mul_assoc,mul_comm (r^a.1.fst)] using hr a v
    _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ lev size) (nonneg a)) (Real.sqrt_nonneg _)

end YM.Integration.WilsonPublicForkWallet
