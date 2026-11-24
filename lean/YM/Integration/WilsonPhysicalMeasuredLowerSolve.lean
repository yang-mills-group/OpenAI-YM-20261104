import YM.Integration.WilsonPhysicalMeasuredLowerPanel

/-! The full physical lower Gram and upper-to-lower matrix are measured together at a real home. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMeasuredLowerSolve
open Function Set Filter Finset Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPhysicalMeasuredLowerPanel (filed reported born)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)}(B:Deck G)(h:ℕ)(a:Axis)(avoid:Finset E4)
variable {D T:ℕ}{U:Type}(cap:h≤D)(d:U→Fin (D+1))(x:(i:U)→(Bel R.family.book).Field (d i))
local notation "I" => Glyph B h

def grade:I⊕U→Fin (D+1)
  | .inl _=>⟨h,Nat.lt_succ_of_le cap⟩
  | .inr j=>d j

def leg:(s:I⊕U)→(Bel R.family.book).Field (grade B h cap d s)
  | .inl i=>named R B h i
  | .inr j=>x j

section Blocks
variable {V W:Type}[Fintype V][DecidableEq V]
def lower (A:Matrix (V⊕W) (V⊕W) ℂ):Matrix V V ℂ:=A.submatrix Sum.inl Sum.inl
def cross (A:Matrix (V⊕W) (V⊕W) ℂ):Matrix V W ℂ:=A.submatrix Sum.inl Sum.inr
def projection (A:Matrix (V⊕W) (V⊕W) ℂ):Matrix V W ℂ:=(lower A)⁻¹*cross A

theorem decoded (A:Matrix (V⊕W) (V⊕W) ℂ)(unit:IsUnit (lower A).det):
    lower A*projection A=cross A:=by
  rw [projection,←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ unit,Matrix.one_mul]

private theorem inverse_at (A:Matrix (V⊕W) (V⊕W) ℂ)(unit:IsUnit (lower A).det):
    ContinuousAt (fun t:Matrix (V⊕W) (V⊕W) ℂ=>(lower t)⁻¹) A:=by
  have inverse:ContinuousAt Ring.inverse (lower A).det:=by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ unit.ne_zero
  have lo:Continuous (fun t:Matrix (V⊕W) (V⊕W) ℂ=>t.submatrix (Sum.inl:V→V⊕W) (Sum.inl:V→V⊕W)):=
    continuous_id.matrix_submatrix _ _
  exact (continuousAt_matrix_inv (lower A) inverse).comp lo.continuousAt

theorem continuous (A:Matrix (V⊕W) (V⊕W) ℂ)(unit:IsUnit (lower A).det):
    ContinuousAt projection A:=by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  change ContinuousAt (fun t:Matrix (V⊕W) (V⊕W) ℂ=>∑k,(lower t)⁻¹ i k*t (Sum.inl k) (Sum.inr j)) A
  apply tendsto_finsetSum
  intro k _
  exact ((continuousAt_pi.mp (continuousAt_pi.mp (inverse_at A unit) i) k)).mul
    ((continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inl k))).continuousAt
end Blocks

local notation "k" => grade B h cap d
local notation "v" => leg R B h cap d x
local notation "predicted" => born R a k v
local notation "table" => reported R F J a avoid k v

theorem born_lower:lower predicted=Matrix.of (reading a (nodes a) (id:I→I)):=by
  ext i j
  exact WilsonOriginalPublicRelativeGramFreePanel.incidence R B h a i j

/-- Includes the unit of the complete lower quotient. The constant precedes
the real home, both cutoff coordinates, every weak/pooled switch and the upper data. -/
theorem original (bliss:Bliss F ℓ arch H)(lead:Leading F J)(m:ℝ→ℕ)
    (mesh:Tendsto (fun r=>R.family.S.a (m r)/r) trail (𝓝 0)):
    ∃C:ℝ,0<C ∧
    Tendsto (fun r=>projection (table (m r) r)) trail (𝓝 (projection predicted)) ∧
    ∀ᶠ r in trail,let A:=table (m r) r
      IsUnit (lower A).det ∧ ‖(lower A)⁻¹‖≤C ∧
      ∀book:Book F (l:=ℓ) H arch D T r,∀side:I⊕U→Bool,
        let A₀:=filed R F J a avoid k v (m r) book side
        Tendsto (fun z=>projection (A₀ z)) (ℓ:Filter (ℕ×ℕ)) (𝓝 (projection A)) ∧
        ∀ᶠ z in (ℓ:Filter (ℕ×ℕ)),IsUnit (lower (A₀ z)).det ∧ ‖(lower (A₀ z))⁻¹‖≤C:=by
  classical
  obtain ⟨c,δ,cp,dp,pay⟩:=WilsonOriginalPublicRelativeGramReference.original a (id:I→I) injective_id
  let bound:ℝ:=∑_i:I,∑_j:I,(Fintype.card I:ℝ)/c
  have nn:0≤bound:=by dsimp [bound];positivity
  have exactFree:=born_lower R B h a cap d x
  have identity:IsUnit (lower predicted).det:=(pay _ (by simpa only [exactFree,Matrix.of_apply,sub_self,norm_zero] using dp.le)).1
  have converge:=WilsonPhysicalMeasuredLowerPanel.leading R F J a avoid k v lead m mesh
  have low(i j:I):Tendsto (fun r=>lower (table (m r) r) i j) trail (𝓝 (reading a (nodes a) (id:I→I) i j)):=by
    have entry:lower predicted i j=reading a (nodes a) (id:I→I) i j:=congrFun (congrFun exactFree i) j
    rw [←entry]
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp converge (Sum.inl i)) (Sum.inl j)
  have joint:=tendsto_pi_nhds.mpr fun i:I=>tendsto_pi_nhds.mpr (low i)
  refine ⟨bound+1,by linarith,(continuous _ identity).tendsto.comp converge,?_⟩
  filter_upwards [Metric.tendsto_nhds.mp joint (δ/2) (half_pos dp),self_mem_nhdsWithin (a:=(0:ℝ))] with r near rp A
  have dist₀:‖(fun i j=>lower A i j)-reading a (nodes a) (id:I→I)‖≤δ/2:=by simpa only [dist_eq_norm] using near.le
  have receipt:=pay (lower A) (dist₀.trans (half_le_self dp.le))
  refine ⟨receipt.1,receipt.2.trans (by linarith),?_⟩
  intro book side A₀
  have cv:=WilsonPhysicalMeasuredLowerPanel.original R F J a avoid k v bliss (m r) rp book side
  refine ⟨(continuous _ receipt.1).tendsto.comp cv,?_⟩
  have narrow:Tendsto (fun z i j=>lower (A₀ z) i j) (ℓ:Filter (ℕ×ℕ)) (𝓝 (fun i j=>lower A i j)):=
    tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>tendsto_pi_nhds.mp (tendsto_pi_nhds.mp cv (Sum.inl i)) (Sum.inl j)
  filter_upwards [Metric.tendsto_nhds.mp narrow (δ/2) (half_pos dp)] with z late
  have dn:‖(fun i j=>lower (A₀ z) i j)-(fun i j=>lower A i j)‖≤δ/2:=by simpa only [dist_eq_norm] using late.le
  have kept:=pay (lower (A₀ z)) ((norm_sub_le_norm_sub_add_norm_sub _ (fun i j=>lower A i j) _).trans (by linarith only [dn,dist₀]))
  exact ⟨kept.1,kept.2.trans (by linarith)⟩

end YM.Integration.WilsonPhysicalMeasuredLowerSolve
