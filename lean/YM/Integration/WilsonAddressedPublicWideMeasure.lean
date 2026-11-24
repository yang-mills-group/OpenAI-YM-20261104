import YM.Integration.WilsonAddressedPublicWideAperture
import YM.Integration.WilsonAddressedPublicWideCards

/-! The before-collar basis-change bound from the literal two-home reflected Wilson measure. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 3800000
namespace YM.Integration.WilsonAddressedPublicWideMeasure
open Set Filter Finset Function Lattice Wilson RG Source Labels Cells OPE Trace.Pilot
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical PhysMS
open FVA2 FVA2.Register Climb GapsContact Next.Rank Maxwell
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonOriginalPublicRelativeGramPins (matrix cutoff)
open WilsonOriginalPublicRelativeGramTransport (transition)
open WilsonOriginalPublicRelativeGramAddresses (ports)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicHomeCard (exponent)
open WilsonAddressedPublicWideCards (filed wage)
open WilsonAddressedPublicWideAperture (zoom)
open WilsonPositionProgramPublicWickGram (vertex apart)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

variable {G:Gauge}(β:Local.Physical.Deck G)(h:ℕ)(ax:Axis)

theorem distinct (ax:Axis):(pointsAt ax).ofLp 0≠(pointsAt ax).ofLp 1:=by
  change -(vertex ax)≠vertex ax
  intro eq
  have zero:=apart ax
  rw [sub_eq_zero.mpr eq.symm] at zero
  have bad:=congrArg norm zero
  simp [basis_norm] at bad

theorem original:
    ∃κ:ℝ,0<κ ∧ ∀(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
      (J:ℝ→tower S)(_ :WilsonPrescription G){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
      {z:Trace.Terrace.Arch R.family}(avoid:Finset E4){scale:ℝ→ℝ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F h scale),
    G.Simple → Bliss F l z H → Leading F J → Coupling G scale → (l:Filter (ℕ×ℕ))≤f.fuse →
    Trace.Terrace.PostT R.family.path.levels → WilsonWindowReportingPace.Slow R.kit →
    ∃(C:ℝ)(k:ℕ),0<C ∧ ∀T:ℕ,∃A:ℝ,0≤A ∧ ∀{V:Type}(law:Filter V){r s:V→ℝ},
    Tendsto r law trail → Tendsto s law trail → ∀ᶠ v in law,
    let τ:=zoom z (r v) (s v)
    let E:=τ/r v
    let K:=(C*E^k*κ)*(C*E^k)
    ∀{D:ℕ}(cap:h≤D)(books:∀b,Book F (l:=l) H z D T (cond b (s v) (r v))),
    (∀b,Housed F (books b)) → ∀branch:Bool→Glyph β h→Bool,
    let expenses:=wage R F J β h cap books branch
    let U:=transition R h J (named R β h) (r v) (s v)
    let den:=(wilson z (r v))^(exponent T h)*(wilson z (s v))^(exponent T h)
    1≤E ∧ ‖U‖≤K*(∑i,∑j,expenses i j) ∧
      ‖U‖*den≤K*(∑i,∑j,(A*‖named R β h i‖)*(A*‖named R β h j‖)) ∧
      ∀ᶠ w:ℕ×ℕ in f.fuse,∀i j,‖cutoff R ax (fun _:Glyph β h=>h) (Γ.date τ)
        (fun _:Unit=>ports R avoid (pointsAt ax) (Γ.date τ) τ) (fun _:Unit=>(1:ℂ))
        (WilsonAddressedPublicPairPins.name R F books ⟨h,Nat.lt_succ_of_le cap⟩ (filed R J β h (r v) (s v)) branch)
        true w i j‖≤expenses i j:=by
  classical
  letI : DecidableEq (Glyph β h) := fun i j=>Classical.propDecidable (i=j)
  obtain ⟨κ,kp,reference⟩:=WilsonOriginalPublicRelativeGramReporting.original β h ax
  refine ⟨κ,kp,?_⟩
  intro R f S F J Z l H z avoid scale Γ simple bliss lead temp below cash slow
  let P:=named R β h
  obtain ⟨C,k,cp,priced⟩:=WilsonOriginalPublicRelativeGramOptical.original R F h J P lead
  refine ⟨C,k,cp,?_⟩
  intro T
  obtain ⟨A,δ,ap,dp,due⟩:=WilsonAddressedPublicWideCards.price R F J Z β h simple bliss lead T
  refine ⟨A,ap,?_⟩
  intro V law r s comes goes
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have endZoom:=(WilsonAddressedPublicWideAperture.approaches F simple bliss comes goes).1
  have positive:∀ᶠ t in trail,0<t:=self_mem_nhdsWithin
  have fine:Tendsto (fun t=>R.family.S.a (Γ.date t)/t) trail (𝓝 0):=by
    apply squeeze_zero' (positive.mono fun t tp=>(div_pos (R.family.S.a_pos _) tp).le) Γ.upper
    simpa only [zero_pow (by decide:2≠0)] using (Coupling.conforms simple temp).pow 2
  have geometry:=WilsonAddressedPublicWideAperture.original F law simple bliss cash slow comes goes T Γ.date fine
    (fun _:Unit=>avoid) (fun _:Unit=>pointsAt ax) (fun _=>distinct ax)
  have actual:=reference R F J avoid Γ simple temp lead
  have close:∀ᶠ t in trail,t∈Ioc (0:ℝ) δ:=Ioc_mem_nhdsGT dp
  filter_upwards [endZoom.eventually actual,endZoom.eventually priced,geometry,comes.eventually close,goes.eventually close,
    comes.eventually link.positive,goes.eventually link.positive,
    comes.eventually ((link.conforms simple).eventually (ge_mem_nhds zero_lt_one))]
      with v ground gates space rp sp gp gs gu τ E K D cap books housed branch expenses U den
  have base:1≤E:=by
    apply (le_div_iff₀ rp.1).mpr
    rw [one_mul]
    apply (le_max_left .. : WilsonThermometerUnitFilingFourPoolClock.outer z 4 (r v)≤τ).trans'
    exact le_mul_of_one_le_right rp.1.le (one_le_pow₀ (one_le_inv₀ gp |>.mpr gu))
  have zp:0<τ:=lt_of_lt_of_le rp.1 (show r v≤τ by simpa only [one_mul] using (le_div_iff₀ rp.1).mp base)
  have home:τ/E=r v:=by dsimp only [E];field_simp [zp.ne',rp.1.ne']
  have fitted:=gates E base
  rw [home] at fitted
  let site:=Γ.date τ
  let o:=fun _:Unit=>ports R avoid (pointsAt ax) site τ
  let μ:=fun _:Unit=>(1:ℂ)
  let ref:=matrix R F ax (fun _:Glyph β h=>h) J (fun i=>P i) τ τ site o μ true
  let ref₀:=matrix R F ax (fun _:Glyph β h=>h) J (fun i=>P i) τ τ site o μ false
  have eq₀:ref=ref₀:=rfl
  have rank:IsUnit ref.det:=by
    rw [eq₀]
    convert ground.2.1 using 1; congr! 4
  have inverse:‖ref⁻¹‖≤κ:=by
    rw [eq₀]
    convert ground.2.2 using 1; congr! 4
  have remote:=WilsonOriginalPublicRelativeGramWide.priced R F ax h J P (r v) τ site o μ rank inverse fitted.1 fitted.2
  let measured:=matrix R F ax (fun _:Glyph β h=>h) J (fun i=>P i) (r v) (s v) site o μ false
  have full:IsUnit measured.det:=by convert remote.1 using 1; congr! 4
  have budget:‖measured⁻¹‖≤K:=by convert remote.2 using 1; congr! 4
  let grade:Fin (D+1):=⟨h,Nat.lt_succ_of_le cap⟩
  let vectors:=filed R J β h (r v) (s v)
  let Y:=WilsonAddressedPublicPairPins.name R F books grade vectors branch
  let arm:=fun b i=>((books b).rows grade).arm (branch b i) (vectors b i)
  have safe:∀i,μ i≠0→Extraction.Order.grid R.family site (o i)∈generic 2:=fun _ _=>ground.1
  have earn:∀ᶠ w:ℕ×ℕ in f.fuse,∀i j,‖cutoff R ax (fun _:Glyph β h=>h) site o μ Y true w i j‖≤expenses i j:=by
    refine eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>?_))
    have g₀:=(space ()).2 (books false) (books true) (housed false) (housed true) grade grade
      (vectors false i) (vectors true j) (branch false i) (branch true j)
    have paid:=WilsonAddressedPublicPairFence.original R F books grade vectors branch cash true i j site o μ
      g₀.1 (fun _=>(space ()).1) (fun _=>g₀.2)
    filter_upwards [paid] with w offered
    simpa only [Y,expenses,wage,o,μ,norm_one,Fintype.sum_unique,one_mul] using offered ax
  have nn:0≤K:=by dsimp only [K];positivity
  have gross:=WilsonOriginalPublicRelativeGramRough.original R F ax h J P (r v) (s v) site o μ Y
    (fun b i=>(arm b i).label) (fun b i=>(arm b i).approaches) (fun b i=>(arm b i).represents)
    below safe expenses earn nn full budget
  have denp:0 ≤ den:=mul_nonneg (pow_nonneg gp.le _) (pow_nonneg gs.le _)
  refine ⟨base,gross,(mul_le_mul_of_nonneg_right gross denp).trans ?_,earn⟩
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ nn
  simp_rw [sum_mul]
  exact sum_le_sum fun i _=>sum_le_sum fun j _=>due _ _ rp sp cap books housed branch i j

end YM.Integration.WilsonAddressedPublicWideMeasure
end
