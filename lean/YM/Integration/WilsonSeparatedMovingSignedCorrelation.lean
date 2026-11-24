import YM.Integration.WilsonSeparatedMovingNullOPE
import YM.Integration.WilsonSeparatedMovingRichVacuum

/-! An actual two-length, signed continuum correlation estimate. Both the
occupied charge and its empty outer reading use the same original field Q.
The gain uses real spatial separation before all near and far locations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMovingSignedCorrelation
open Filter Function Set Spec OPE OPE.Orbits PhysMS Trace.Pilot Pert Pert.Position RG17 Extraction Table Climb
open MS MS.Land MS.Menus MS.Local.Physical OPE.Nesting OPE.Levy
open Frontier6.Road PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonSeparatedMovingRichGeometry WilsonSeparatedMovingRichVacuum WilsonSeparatedMovingNullOPE
open scoped BigOperators Classical Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {V:Table R.family.book}
variable {I E:Type} [Fintype I] [Fintype E] {d:I→ℕ} {e:E→ℕ}

private lemma cancellation (F:Final R.family f V) (hG:G.Simple)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (x:I→E4) (legal:Injective x)
    (v:Labels V d) (y:E→E4) (w:Labels V e) {c H:ℝ}
    (occupied:‖formula F Q x 0 v y w 0 none‖≤c)
    (vacant:‖formula F Q x 0 v Short.gapPos (voices (blank V)) 0 none‖≤c)
    (budget:‖upon V 0 0 y w (V.unit 0)‖≤H) :
    ‖whole V x v y w-Orbits.moment V x v*upon V 0 0 y w (V.unit 0)‖≤c*(1+H) := by
  let word (i:I):V.Tag:=⟨d i,v i⟩
  let ext:=upon V 0 0 y w (V.unit 0)
  obtain ⟨z,origin⟩:=RG12.Kintsugi.Spot.unit_desc (C:=R.family) (S:=V) hG (by norm_num : (0:ℕ)<4) (Q.fresh 0 x 0 v)
  rw [WilsonMacroscopicVacuumFactor.grade_zero,origin,map_smul] at occupied vacant
  change ‖whole V x v y w-z*ext‖≤c at occupied
  change ‖whole V x v Short.gapPos (voices (blank V))-z*upon V 0 0 Short.gapPos (voices (blank V)) (V.unit 0)‖≤c at vacant
  have obs:whole V x v Short.gapPos (voices (blank V))=Orbits.moment V x v := Short.tagged F word x none legal
  rw [obs,show upon V 0 0 Short.gapPos (voices (blank V)) (V.unit 0)=1 from Short.vacuum F none 0 _ (blank V),mul_one] at vacant
  change ‖whole V x v y w-Orbits.moment V x v*ext‖≤_
  have cp:0≤c:=(norm_nonneg _).trans occupied
  calc
    _≤‖whole V x v y w-z*ext‖+‖z*ext-Orbits.moment V x v*ext‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤c+c*H := add_le_add occupied (by rw [←sub_mul,norm_mul,norm_sub_rev z];exact mul_le_mul vacant budget (norm_nonneg _) cp)
    _=_ := by ring

private lemma fee (hG:G.Simple) {g:ℝ→ℝ} (hg:Coupling G g) {a ζ γ:ℝ}
    (margin:γ<(1-a)*ζ) (S:ℝ) (k:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ r in trail,(r/r^a)^ζ*S≤ε*g r^k*r^γ := by
  filter_upwards [subpower_payment hg hG S ((1-a)*ζ-γ) (sub_pos.mpr margin) ε ep k,length_rate.pos] with r price rp
  change 0<r at rp
  have clock:(r/r^a)^ζ=r^((1-a)*ζ-γ)*r^γ := by
    rw [show r/r^a=r^(1-a) by rw [Real.rpow_sub rp,Real.rpow_one],←Real.rpow_mul rp.le,←Real.rpow_add rp];congr 1;ring
  rw [clock,mul_comm _ S,←mul_assoc];exact mul_le_mul_of_nonneg_right price (Real.rpow_nonneg rp.le _)

/-- The unit/far measurement is made on the original law at the same time as
the genuine near moment. No conditioning or factorization assumption occurs. -/
theorem original (hG:G.Simple) (F:Final R.family f V) (fac:Facilities R.family f V)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower V) (lead:Leading F J)
    {A:(Bel R.family.book).Hierarchy} (obey:∀ h:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) h)
    (B:Deck G) (D:ℕ) (φ:Test 2) (v:(i:I)→Free R.family (d i)) {a M η γ:ℝ}
    (ap:0<a) (top:a<1) (mp:0≤M) (ηp:0<η) (gap:γ<1-a) {g:ℝ→ℝ} (hg:Coupling G g) (k:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ r in trail,∀ x:I→E4,WithinRoom r M η x 0→∀ u∈tsupport φ,∀ b:Glyph B D,
      let y:=far (r^a) u
      let w:=fields B D b J (r^a)
      let ins:=Frame.born J r v
      ‖whole V x ins y w-Orbits.moment V x ins*upon V 0 0 y w (V.unit 0)‖≤ε*g r^k*r^γ := by
  have positive:0<1-a := sub_pos.mpr top
  have ratio:γ/(1-a)<1 := (div_lt_iff₀ positive).mpr (by simpa only [one_mul] using gap)
  obtain ⟨ζ,above,below⟩:=exists_between ratio
  have margin:γ<(1-a)*ζ := by rw [mul_comm];exact (div_lt_iff₀ positive).mp above
  obtain ⟨H,_,bounded⟩:=WilsonSeparatedMovingRichVacuum.original B F J lead D φ obey
  let m:=(fun _:Fin 1=>D)
  let probe (b:Glyph B D) (i:Fin 1):Free R.family (m i) := WilsonMacroscopicRichFree.basis R.family B D b
  have actual (b:Glyph B D):=WilsonSeparatedMovingProfileOPE.original F Q J lead fac φ v (probe b) ap top mp ηp 0 below
  have empty:=WilsonSeparatedMovingNullOPE.original F Q J lead fac v ap top mp ηp below
  have time:=PhysMS.length_rate.rpow a
  have rt:Tendsto (fun r:ℝ=>r^a) trail trail := tendsto_nhdsWithin_iff.mpr
    ⟨time.tends (by linarith only [ap]) PhysMS.to_log_zoom,time.pos⟩
  filter_upwards [Filter.eventually_all.mpr actual,empty,rt.eventually bounded,fee hG hg margin (1+H) k ep,length_rate.pos] with r sold absent arm sum rp x hx u hu b
  change 0<r at rp
  have honest:Injective x := by
    intro i j eq
    by_contra ne
    have sep:=hx.spaced i j ne
    rw [eq,sub_self,norm_zero] at sep
    exact (not_le_of_gt (mul_pos ηp rp)) sep
  apply (cancellation F hG Q x honest (Frame.born J r v) (far (r^a) u) (fields B D b J (r^a)) _ (absent x hx) (arm b u hu)).trans sum
  have same:Frame.born J (r^a) (probe b)=fields B D b J (r^a) := rfl
  have occupied:=sold b x hx u hu none
  simp only [same,Nat.cast_zero,zero_add] at occupied
  exact occupied

end YM.Integration.WilsonSeparatedMovingSignedCorrelation
