import YM.Integration.WilsonThermometerWeakCornerGeometry
import YM.Integration.WilsonThermometerWeakCornerNorm
import YM.Integration.WilsonThermometerWeakCornerSalary
import YM.Integration.WilsonThermometerWeakLogPrice

/-! All normalized shape derivatives of a physical proper face on a
fixed compactum, with its literal original stationary exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCornerPhysical
open Function Filter Finset Set Table Spec Extraction RG Lattice Trace Trace.Pilot
open GapsContact GapsContact.Ascent GapsContact.Seams Next.UVStress OPE OPE.Orbits
open PhysicalNext.Repeat.Legato Climb PhysMS Maxwell EveryPhase Frontier6 XSpace XSpace.Normalize
open WilsonThermometerWeakCornerJets WilsonThermometerWeakCornerWatch
open WilsonThermometerWeakWatchedFaces WilsonPositionThermometerCapStation
open WilsonPositionCapTransport (Book)
open scoped Topology Classical BigOperators ContDiff
universe u
variable {G:Gauge}{R:Run G}{T:Campaign R}{W₀:Campaign.Pillars R T}
    {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (P:ℝ→tower S)(V:Store G){H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
    {n c:ℕ}

private theorem saved (d:Fin n→Fin (c+1))(Z:Group R.family c)
    (w:∀i,(Bel R.family.book).Field (d i)){r:ℝ}(s:Finset (Fin n))
    (proj:∀i,S.project (d i) (Z.lift (index Z (d i)) (Z.change (d i) (w i)))=
      WilsonNormalizedReflectedForm.field F P V true (d i) r (w i)):
    near (S:=S) R (fun i=>(d i).val) (mask R d s (fun i=>Z.lift (index Z (d i)) (Z.change (d i) (w i)))) =
      fun i=>if i∈s then ⟨d i,WilsonNormalizedReflectedForm.field F P V true (d i) r (w i)⟩ else ⟨d i,S.unit (d i)⟩:=by
  funext i
  by_cases hi:i∈s
  · simp only [near,mask,hi,if_true,Table.classTokens]
    exact congrArg (Sigma.mk (d i).val) (proj i)
  · simp only [near,mask,hi,if_false,Table.classTokens]
    rfl

theorem original (simple:G.Simple){e:ℝ}
    (funded:WilsonLimitConstruction.FundedOriginalProperties.{u} simple e W₀)(L:Almanac F)(found:Completed F L)
    (A:ℝ→Group R.family c)(paid:Book (f:=f) (l:=l) (H:=H) A P)(lead:Leading F P)
    (d:Fin n→Fin (c+1))(w:∀i,(Bel R.family.book).Field (d i))
    (W:Watch R.family)(K:Set (Points n))(compact:IsCompact K)(cleared:K⊆conf n)
    (k:ℕ){σ:ℝ}(sp:0<σ):
    ∀ᶠ r in trail,∀s:Finset (Fin n),∀x∈K,
      let input:=heard (S:=S) R d (WilsonPositionCorrectedCap.adjusted F P V A r) w W r s
      ContDiffAt ℝ ∞ input x ∧ ‖iteratedFDeriv ℝ k input x‖≤r^(-σ):=by
  let Z:=WilsonPositionCorrectedCap.adjusted F P V A
  let y:=fun i:Fin W.n=>W.held i.succ
  let arms:=outside (S:=S) R W
  let quota:=1+∑ i,‖w i‖
  have hp:0≤quota:=by dsimp [quota]; positivity
  have bounds (i:Fin n):‖w i‖≤quota:=(Finset.single_le_sum (f:=fun j=>‖w j‖) (fun j _=>norm_nonneg (w j)) (mem_univ i)).trans
    (le_add_of_nonneg_left zero_le_one)
  obtain ⟨gap,gp,room⟩:=WilsonThermometerWeakCornerGeometry.original W K compact cleared
  let rolled:=WilsonThermometerWeakCornerRows.original F simple funded L found
  obtain ⟨B,m,bp,heads⟩:=WilsonThermometerWeakCornerNorm.original F rolled (fun i=>(d i).val) (fun j=>(W.q j).1) k gp
  obtain ⟨U,up,fees⟩:=WilsonThermometerWeakCornerSalary.original F P V lead (fun i=>(d i).val) hp
  have ext:0≤billSlots F 1 arms:=billSlots_pos ..
  have a:=half_pos sp
  have small:=WilsonThermometerWeakLogPrice.original (m:=m) a
  let thick:=B*2^m*U*billSlots F 1 arms
  have amp:∀ᶠr in trail,thick≤r^(-(σ/2)) :=(tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr a)).eventually_ge_atTop thick
  have under:∀ᶠ r in trail,r<1:=(eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have proj:=WilsonPositionCorrectedCap.mixed F P V A paid lead d w 0
  filter_upwards [proj,room,fees,small,amp,under,self_mem_nhdsWithin] with r pr fit wage pl inv r1 rp
  intro s x hx
  let near₀:=near (S:=S) R (fun i=>(d i).val) (mask R d s
    (fun i=>(Z r).lift (index (Z r) (d i)) ((Z r).change (d i) (w i))))
  have same:=saved F P V d (Z r) w (r:=r) s (fun i=>(pr.2.2.2.2.1 (d i)).2.2 (w i) |>.symm)
  have size:billSlots F r near₀≤U:=by
    change billSlots F r (near (S:=S) R _ _)≤U
    rw [same]
    exact wage s true w bounds
  have clear:Injective (sites r x y):=by
    intro i j eq
    by_contra neq
    have info:gap*Sum.elim (fun _:Fin n=>r) (fun _:Fin W.n=>(1:ℝ)) i≤‖sites r x y i-sites r x y j‖:=fit x hx neq
    rw [eq,sub_self,norm_zero] at info
    have z:0<Sum.elim (fun _:Fin n=>r) (fun _:Fin W.n=>(1:ℝ)) i:=by
      cases i with
      | inl i=>exact rp
      | inr j=>exact zero_lt_one
    exact (mul_pos gp z).not_ge info
  have eq:=WilsonThermometerWeakCornerWatch.face R F d (Z r) w W r s clear
  have sm:=smooth F none near₀ arms y r clear
  refine ⟨sm.congr_of_eventuallyEq eq,?_⟩
  rw [(EventuallyEq.iteratedFDeriv ℝ eq k).eq_of_nhds]
  have sprice:=heads r ⟨rp,r1.le⟩ 1 ⟨r1.le,le_rfl⟩ x y (fit x hx) none near₀ arms (fun _=>rfl) (fun _=>rfl)
  calc
    _ ≤ B*dock r^m * billSlots F r near₀ *billSlots F 1 arms:=sprice
    _ ≤ B*(2^m*r^(-(σ/2)))*U*billSlots F 1 arms:=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left pl (zero_le_one.trans bp)) size
        (billSlots_pos ..) (mul_nonneg (zero_le_one.trans bp) (mul_nonneg (by positivity) (Real.rpow_nonneg (show 0≤r from rp.le) _)))) ext
    _ = thick*r^(-(σ/2)):=by dsimp [thick];ring
    _ ≤ r^(-(σ/2))*r^(-(σ/2)):=mul_le_mul_of_nonneg_right inv (Real.rpow_nonneg (show 0≤r from rp.le) _)
    _ = _:=by rw [←Real.rpow_add (show 0<r from rp)];congr 1;ring

end YM.Integration.WilsonThermometerWeakCornerPhysical
end
