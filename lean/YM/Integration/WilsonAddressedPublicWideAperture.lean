import YM.Integration.WilsonAddressedPublicHomeWidth
import YM.Integration.WilsonAddressedPublicPairAperture
import YM.Integration.WilsonViewerReportingGrid

/-! A common, polynomially widened reporting grid for the two original moving radii. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
namespace YM.Integration.WilsonAddressedPublicWideAperture
open Set Finset Filter Function Lattice Wilson RG Source Cells OPE Extraction Spec
open PhysicalNext.Repeat.Legato Table Climb GapsContact Trace.Pilot Trace.Terrace Maxwell XSpace
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicSelfCards (width)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonOriginalPublicRelativeGramAddresses (ports)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Arch R.family}
local notation "a" => R.family.S.a
local notation "g" => wilson z

def zoom (z:Arch R.family)(r s:ℝ):ℝ:=max (outer z 4 r) (outer z 4 s)

theorem approaches {V:Type}{law:Filter V}(simple:G.Simple)(bliss:Bliss F l z H)
    {r s:V→ℝ}(comes:Tendsto r law trail)(goes:Tendsto s law trail):
    Tendsto (fun v=>zoom z (r v) (s v)) law trail ∧
      Tendsto (fun v=>max (outer z 2 (r v)) (outer z 2 (s v))/zoom z (r v) (s v)) law (𝓝 0):=by
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have good:=longer F simple bliss 4
  have left:=good.comp comes
  have right:=good.comp goes
  have r₀:Tendsto (fun v=>outer z 4 (r v)) law (𝓝 0):=left.mono_right nhdsWithin_le_nhds
  have s₀:Tendsto (fun v=>outer z 4 (s v)) law (𝓝 0):=right.mono_right nhdsWithin_le_nhds
  have positive:∀ᶠ v in law,0<zoom z (r v) (s v):=
    (left.eventually self_mem_nhdsWithin).mono fun v h=>lt_of_lt_of_le h (le_max_left ..)
  have endZoom:Tendsto (fun v=>zoom z (r v) (s v)) law trail:=by
    exact tendsto_nhdsWithin_iff.mpr ⟨by simpa [zoom] using r₀.max s₀,positive⟩
  have gross:Tendsto (fun v=>max ((g (r v))^2) ((g (s v))^2)) law (𝓝 0):=by
    simpa using (((link.conforms simple).comp comes).pow 2).max (((link.conforms simple).comp goes).pow 2)
  refine ⟨endZoom,squeeze_zero' ?_ ?_ gross⟩
  · filter_upwards [comes.eventually self_mem_nhdsWithin,comes.eventually link.positive,positive] with v rp gp zp
    exact div_nonneg (le_trans (show 0 ≤ outer z 2 (r v) from mul_nonneg rp.le (by positivity)) (le_max_left ..)) zp.le
  filter_upwards [comes.eventually self_mem_nhdsWithin,goes.eventually self_mem_nhdsWithin,
    comes.eventually link.positive,goes.eventually link.positive,positive] with v rp sp rg sg zp
  apply (div_le_iff₀ zp).mpr
  let M:=max ((g (r v))^2) ((g (s v))^2)
  have each {h:ℝ}(hp:0<h)(gp:0<g h)(upper:outer z 4 h ≤zoom z (r v) (s v))(small:(g h)^2≤M):
      outer z 2 h≤ M*zoom z (r v) (s v):=by
    have eq:outer z 2 h=(g h)^2*outer z 4 h:=by unfold outer;field_simp [gp.ne']
    rw [eq]
    exact mul_le_mul small upper (mul_nonneg hp.le (by positivity)) ((sq_nonneg _).trans small)
  exact max_le (each rp rg (le_max_left ..) (le_max_left ..)) (each sp sg (le_max_right ..) (le_max_right ..))

theorem original {V I:Type}[Fintype I](law:Filter V)(simple:G.Simple)(bliss:Bliss F l z H)
    (cash:PostT R.family.path.levels)(slow:WilsonWindowReportingPace.Slow R.kit)
    {r s:V→ℝ}(comes:Tendsto r law trail)(goes:Tendsto s law trail)(T:ℕ)
    (sites:ℝ→ℕ)(fine:Tendsto (fun τ=>a (sites τ)/τ) trail (𝓝 0))
    (avoid:I→Finset E4)(points:I→Points 2)(apart:∀i,(points i).ofLp 0≠(points i).ofLp 1):
    ∀ᶠ v in law,let τ:=zoom z (r v) (s v)
    ∀i:I,let p:=ports R (avoid i) (points i) (sites τ) τ
    ‖R.family.S.gridPoint (sites τ) (p 0-p 1)‖≤1 ∧
    ∀{D D':ℕ}(B:Book F (l:=l) H z D T (r v))(B':Book F (l:=l) H z D' T (s v)),
    Housed F B → Housed F B' → ∀(d:Fin (D+1))(e:Fin (D'+1))(x:S.Field d.val)(y:S.Field e.val)(b c:Bool),
    let m:=min (width F B d x b) (width F B' e y c)
    0 < m ∧ 2*a (m-1)<‖R.family.S.gridPoint (sites τ) (p 0)-R.family.S.gridPoint (sites τ) (p 1)‖:=by
  obtain ⟨M,mp,money⟩:=WilsonAddressedPublicHomeWidth.original F simple bliss cash slow T (p:=1) one_pos
  obtain ⟨lands,room⟩:=approaches F simple bliss comes goes
  let top:=fun v=>zoom z (r v) (s v)
  let wall:=fun v=>M*max (outer z 2 (r v)) (outer z 2 (s v))
  have cheap:Tendsto (fun v=>wall v/top v) law (𝓝 0):=by simpa only [wall,top,mul_div_assoc,mul_zero] using room.const_mul M
  have space:=WilsonAddressedPublicPairAperture.original R law (fun v=>sites (top v)) top wall
    (lands.eventually self_mem_nhdsWithin) (lands.mono_right nhdsWithin_le_nhds) (fine.comp lands) cheap avoid points apart
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  filter_upwards [space,comes.eventually money,goes.eventually money,comes.eventually link.positive,goes.eventually link.positive]
    with v placed left right rg sg τ i p
  refine ⟨(placed i).1,?_⟩
  intro D D' B B' hB hB' d e x y b c m
  obtain ⟨lp,lb⟩:=left B hB d x b
  obtain ⟨rp,rb⟩:=right B' hB' e y c
  have bill {n:ℕ}{h:ℝ}(gp:0<g h)(bound:a (n-1)*((g h)^2)^(1:ℝ)≤h*M):a (n-1)≤M*outer z 2 h:=by
    simp only [Real.rpow_one] at bound
    unfold outer
    rw [inv_pow,←div_eq_mul_inv,←mul_div_assoc,(le_div_iff₀ (pow_pos gp 2))]
    simpa only [mul_comm M h] using bound
  have paid:a (m-1)≤wall v:=by
    by_cases le:width F B d x b ≤ width F B' e y c
    · change a (min _ _-1) ≤ _
      rw [min_eq_left le]
      exact (bill rg lb).trans (mul_le_mul_of_nonneg_left (le_max_left ..) (zero_le_one.trans mp))
    · change a (min _ _-1) ≤ _
      rw [min_eq_right (le_of_not_ge le)]
      exact (bill sg rb).trans (mul_le_mul_of_nonneg_left (le_max_right ..) (zero_le_one.trans mp))
  exact ⟨lt_min lp rp,(mul_le_mul_of_nonneg_left paid (by norm_num:0≤(2:ℝ))).trans_lt (placed i).2⟩

end YM.Integration.WilsonAddressedPublicWideAperture
end
