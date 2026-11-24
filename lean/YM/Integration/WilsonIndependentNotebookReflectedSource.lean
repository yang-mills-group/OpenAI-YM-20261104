import YM.WilsonCoeffUV.Horizon.TurnLayouts
import YM.Integration.WilsonIndependentNotebookDoseReturn

/-! Signed finite stencil symmetry on the inherited unmarked story, and
the corresponding full cover projection at the same date. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookReflectedSource
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Wheel.Motion
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Classical
variable {G:Gauge}{h k l e D N m:ℕ}{F:Labels.Frame G h}

/-- Comparison on each actual ordinary torus, with the same test, reflected
rail and all thermal coefficients. These fields can carry arbitrary older deposits. -/
def Paired (s:Signed)(P Q:TowerS G D):Prop:=∀ n:Side,Wreathe (P.1 n) (Q.1 n) s

theorem projection (H:Hol G)(s:Signed)(clear:h<D){P Q:TowerS G D}
    (left:On k P)(right:On l Q)(given:Paired s P Q):
    opal F Q=paintC F s *ᵥ opal F P:=by
  funext i
  ext1 e
  simp only [opal,coeff_mk,Matrix.mulVec,dotProduct,map_sum,Cosmos.paintC,Matrix.of_apply,coeff_C_mul]
  apply glean_spin F H s clear
  intro j _ r _
  obtain ⟨a,b,ha,hb⟩:=solo_stretch left j r
  obtain ⟨c,d,hc,hd⟩:=solo_stretch right j r
  exact ⟨solo_mercy left right s given j r,solo_mural left _ _,solo_mural right _ _,a,c,b,d,ha,hc,hb,hd⟩

theorem minus (s:Signed){X Y P Q:TowerS G D}(lx:On k X)(ly:On k Y)(lp:On l P)(lq:On l Q)
    (xy:Paired s X Y)(pq:Paired s P Q):Paired s (X-P) (Y-Q):=by
  intro n c Z I z U V eqv
  change train (spool _) (flash (jot c (Y.1 n-Q.1 n))) =
    train (spool _) (flash (jot (spinV s D c) (X.1 n-P.1 n)))
  rw [map_sub,map_sub,flash_sub (finite_shell (jot_length _ (ly.launch n))) (finite_shell (jot_length _ (lq.launch n))),
    flash_sub (finite_shell (jot_length _ (lx.launch n))) (finite_shell (jot_length _ (lp.launch n))),map_sub,map_sub,
    xy n c eqv,pq n c eqv]

theorem transferred (A:Levels G)(O:ChartRatio G)(g:G.Simple)(hc:LocalRatio O)(live:m<N)
    (s:Signed){P Q:TowerS G D}(left:On k P)(right:On k Q)(given:Paired s P Q):
    Paired s (Spout A O N m h k P) (Spout A O N m h k Q):=by
  let K:=ll A m
  let k₀:=A.clock.kernel
  let f:=freeForms A N (m+1)
  let c:=freeForms A N m
  let pipes:=roam A N m
  let T (n:Side):=(story A O N (m+1)).1 (n*K.L)
  let R (n:Side)(Y:TowerS G D):=collarT K k₀ O f pipes k D (n:=n) (T n) (Y.1 (n*K.L))
  have old:=Bank.old A O g hc N (m+1) live
  have shape (n:Side)(Y:TowerS G D)(hy:On k Y):shellK k (R n Y):=
    pin_test K k₀ O f pipes k k hc _ _ (old.basis _).lamp (hy.launch _)
  intro n
  have paid:Wreathe (R n P) (R n Q) s:=
    bells_act K k₀ O f c pipes k hc (A.blocks m 0).branches ((cond_laws A m N).1 n (n*K.L) rfl)
      (horizon_step A m N live n (n*K.L) rfl) (age_sym A ..) _ (old.basis _) s
      (left.launch _) (right.launch _) (left.evenS _) (right.evenS _) (given _)
  have prime:constantCoeff (ratioHigh A O N m)=1:=back_cc (angle_tilt g hc live)
  have moved:=wreathe_mix paid (shape n P left) (shape n Q right) prime
  exact swellG moved (mix_length (shape n P left)) (mix_length (shape n Q right)) (gradeH K h k)

end YM.Integration.WilsonIndependentNotebookReflectedSource
