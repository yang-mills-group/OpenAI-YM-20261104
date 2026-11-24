import YM.Integration.WilsonCenteredNestedDepositedField

/-! Undo the child's one physical rotation and real branch at the parent.
The final original grade-m detector annihilates strictly lower raw
components only after the full lower-grade child has been inserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTerminalOrbit
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open WilsonCenteredNestedProjectedShadow WilsonCenteredNestedRealOrbit
open scoped Classical Topology BigOperators ComplexConjugate
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def out (d:ℕ) (k:Ortho) (b:Bool) (v:S.Field d) : S.Field d :=
  if b then S.conj F.room.kernel.spin d (F.sector.turns.act d k v) else F.sector.turns.act d k v

def into (d:ℕ) (k:Ortho) (b:Bool) (v:S.Field d) : S.Field d :=
  F.sector.turns.act d k⁻¹ (if b then S.conj F.room.kernel.spin d v else v)

def scalar (b:Bool) (c:ℂ) : ℂ := if b then conj c else c

include Q in
lemma returns (d:ℕ) (k:Ortho) (b:Bool) (v:S.Field d) : into F d k b (out F d k b v)=v := by
  have back (u:S.Field d) : F.sector.turns.act d k⁻¹ (F.sector.turns.act d k u)=u := by
    rw [←Q.law.group,inv_mul_cancel,Q.law.fixes]
  cases b
  · exact back v
  · change F.sector.turns.act d k⁻¹ (S.conj F.room.kernel.spin d (S.conj F.room.kernel.spin d (F.sector.turns.act d k v)))=v
    rw [Table.reflect_star,back]

lemma currency {I : Type} [Fintype I] {d:I→ℕ} (P:Prescription F.sector.derivatives) (H:ℕ)
    (x:I→E4) (v:Labels S d) (o:E4) (k:Ortho) (b:Bool) :
    restored F P H x v o k b = out F H k b (shadowOld P H (Ortho.move k⁻¹ ∘ x) (Ortho.move k⁻¹ o)
       (fun i=>into F (d i) k b (v i))) := by
  cases b
  · have hh : roll F.sector.turns k⁻¹ v = fun i=>into F (d i) k false (v i) := by
      funext i; rfl
    change F.sector.turns.act H k (shadowOld P H _ _ (roll F.sector.turns k⁻¹ v))=_
    rw [hh]
    rfl
  · have hh : roll F.sector.turns k⁻¹ (bar F.room.kernel.spin v) = fun i=>into F (d i) k true (v i) := by
      funext i; rfl
    change S.conj F.room.kernel.spin H (F.sector.turns.act H k (shadowOld P H _ _ (roll F.sector.turns k⁻¹ (bar F.room.kernel.spin v))))=_
    rw [hh]
    rfl

include Q in
lemma rise {d h:ℕ} (dh:d≤h) (v:S.Field d) (k:Ortho) (b:Bool) :
    out F h k b (F.sector.derivatives.rise dh v) = F.sector.derivatives.rise dh (out F d k b v) := by
  cases b
  · exact Q.law.filtered .. 
  · change S.conj F.room.kernel.spin h (F.sector.turns.act h k (F.sector.derivatives.rise dh v))=_
    rw [Q.law.filtered,Q.stands.realInc]
    rfl

lemma add_smul {I:Type} (A:Finset I) (d:ℕ) (c:I→ℂ) (u:I→S.Field d) (k:Ortho) (b:Bool) :
    out F d k b (∑i∈A,c i • u i) = ∑i∈A,scalar b (c i) • out F d k b (u i) := by
  cases b <;> simp [out,scalar,map_sum]

lemma lower {m:ℕ} (c:Q.channels m) (i:Mode F.sector.derivatives) (low : i.1 < m) (k:Ortho) (b:Bool) :
    read F Q m m c (out F m k b (Q.port.loaded i m))=0 := by
  rw [cost Q.port i (show i∈bands F.sector.derivatives m from (full_bands ..).mpr low.le),rise F Q]
  change (Q.basis m).coord c ((Q.stratum m).subtype.leftInverse (Q.cutTest m m (F.sector.derivatives.rise low.le _)))=0
  rw [Q.cut_rise,Q.kills_lower _ _ low]
  simp

end YM.Integration.WilsonCenteredNestedTerminalOrbit
