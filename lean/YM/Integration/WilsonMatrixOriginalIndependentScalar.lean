import YM.Integration.WilsonMatrixOriginalIndependentFields

/-! Every subcritical source of the independent deck stays a scalar through the
horizon lift and the actual finite Wick conversion of the booked Wilson columns. -/
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentScalar
open Lattice Wilson RG Precision Maxwell Labels FVA2 FVA2.Warehouse Filter
open Function Finset MS.Local.Physical MS.Theater MS.Menus
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open PhysicalNext.Repeat.Legato WilsonMatrixOriginalIndependentFields
open scoped Classical BigOperators

variable {G:Gauge} (B:Deck G)

/-- The raised polynomial has exactly the original constant as its full raw value. -/
theorem raised (simple:G.Simple) (i:Glyph B 4) (low:i.1.val<4):
    ∃c:ℂ,field B 4 i=c • Labels.unit G 4:=by
  obtain ⟨c,once⟩:=UVNext.FreeStress.just_one simple low
    (Warehouse.label B i.1.val i.2.1.val i.2.2)
  refine ⟨c,?_⟩
  unfold WilsonMatrixOriginalIndependentColumns.field
  rw [once,map_smul]
  rfl

open PertExtension.Heat Next.Rank.Normal
private theorem empty_column {K J:Type*} [Fintype J] [DecidableEq J]
    (M:PertExtension.Heat.Frame K J) (Q:Symmetric K) (z:J) (h:M.slots z=0):
    M.inverse Q (Pi.single z 1)=Pi.single z 1:=by
  let e:J→ℂ:=Pi.single z 1
  have he:M.conversion Q e=e:=by
    change (∑i,e i • M.joint (milk Q (M.basis i)))=e
    rw [sum_eq_single_of_mem z (mem_univ _) (fun i _ different=>?_) ]
    · rw [show e z=1 from Pi.single_eq_same ..,one_smul]
      funext j
      exact M.coefficientMatrix (Q:=Q) (i:=z) (j:=j) (h ▸ Nat.zero_le _)
    · rw [show e i=0 from Pi.single_eq_of_ne different 1,zero_smul]
  exact (M.conversion Q).injective (((M.conversion Q).apply_symm_apply e).trans he.symm)

/-- The original finite Wick conversion preserves the unit at every horizon. -/
theorem flat (V:Warehouse G) (d:ℕ):
    (V.scopeW d).inverse (inftyQ G) (V.scene d).e0=(V.scene d).e0:=
  empty_column (V.scopeW d) (inftyQ G) 0 (congrArg Prod.snd (V.scene d).zero_degree)

/-- No finite heat counterterm on a lower-grade glyph can change the placed Wilson field. -/
theorem column (V:Warehouse G) (simple:G.Simple) (i:Glyph B 4) (low:i.1.val<4):
    ∃c:ℂ,WilsonMatrixOriginalIndependentColumns.column V B 4 i=c • (V.scene 4).e0:=by
  obtain ⟨c,field_eq⟩:=raised B simple i low
  refine ⟨c,?_⟩
  unfold WilsonMatrixOriginalIndependentColumns.column
  rw [field_eq,map_smul,(V.scene 4).coords_unit,map_smul,flat]

end YM.Integration.WilsonMatrixOriginalIndependentScalar
