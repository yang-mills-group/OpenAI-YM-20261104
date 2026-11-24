import YM.Integration.WilsonPhysicalExteriorGradeReadout
import YM.Integration.WilsonPhysicalExteriorGradeCoefficient
import YM.Integration.MSMeasuredEngineering

/-! Solve the lower output on the actual common Wilson/Maxwell
receivers at the first omitted engineering grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorSolvedGrade
open Filter Function Matrix PowerSeries Lattice
open MS MS.Dial MS.Land MS.Menus MS.Tide MS.Rake FVA2 FVAAlt2 FVAAlt2.Lobby
open Pert Pert.Position Pert.Scale Extra.FD OPE.Levy RG11.Fields PhysicalNext.Repeat.Legato
open MSCutoffGerms MSMeasuredGermSeries MSMeasuredEngineering
open WilsonPhysicalExteriorFieldGram WilsonPhysicalExteriorPairedLimit WilsonPhysicalExteriorReceivedGerms
open WilsonPhysicalExteriorGradeReadout
open scoped BigOperators Classical Topology
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}
variable (R:Run G) (Q:Prescription B) (T:Trial ℕ (Fin 2))

private theorem square_germ (h:ℕ) (μ ν:ℝ) :
    gather (l:=atTop) (observed R Q T h h ν) = gather (step Q T h μ ν)*
      gather (transported R Q T h h μ ν)*(gather (step Q T h μ ν)).transpose := by
  rw [show observed R Q T h h ν=_ from funext (square R Q T h μ ν)]
  rw [multiply,multiply];rfl

private theorem edge_germ (h:ℕ) (μ ν:ℝ) :
    gather (l:=atTop) (edge R Q T h ν) =
      (gather (l:=atTop) (lower Q T h μ ν)*gather (l:=atTop) (transported R Q T h h μ ν)+
        gather (l:=atTop) (boundary Q T h μ ν)*gather (l:=atTop) (inner R Q T h μ ν))*
          (gather (l:=atTop) (step Q T h μ ν)).transpose := by
  rw [show edge R Q T h ν=_ from funext (outlet R Q T h μ ν)]
  rw [multiply,MSMeasuredEngineering.add,multiply,multiply];rfl

variable {R Q T} {M:MS_Data G O} {p q:E4}
theorem measured (V:Warehouse G) (hp:p≠q) (reads:Read R M Q T (Fountain.metric (couple p q)))
    (h:ℕ) (μ s:ℝ) (prior:∀ a b:Glyph B h,∀ k:ℕ,
      Moderate atTop T.profile.θ (fun i=>coeff k (step Q T h μ (μ+s) i a b))) :
    ∀ v:Plaid B (h+1),∀ a:Glyph B h,∀ k:ℕ,
      Moderate atTop T.profile.θ (fun i=>coeff k (lower Q T h μ (μ+s) i v a)) := by
  let ν:=μ+s
  let ht:=reads.1
  let f:=MSMeasuredEngineering.cast T ht
  let A:=changed reads h h μ ν
  let C:=receiver reads h h ν
  obtain ⟨U,hu⟩:=lift_entries T ht (step Q T h μ ν) prior
  have ha:A.map f=gather (l:=atTop) (transported R Q T h h μ ν) := by
    apply Matrix.ext;intro a b;exact changed_entry reads h h μ ν a b
  have hc:C.map f=gather (l:=atTop) (observed R Q T h h ν) := by
    apply Matrix.ext;intro a b;exact receiver_entry reads h h ν a b
  have hL:C=U*A*U.transpose:=by
    apply MSGradedReceiverRigidity.same f (PowerSeries.map_injective (ring ht).subtype (ring ht).subtype_injective)
    rw [hc,square_germ,←hu,←ha,Matrix.map_mul,Matrix.map_mul];rfl
  have top (v w:Plaid B (h+1)) (i:ℕ) :
      boundary Q T h μ ν i v w=pay Q (μ-T.profile.θ i) (ν-T.profile.θ i) (FVAAlt2.Lobby.spacing T i)
        (owner (Land.read v)) (Land.read w) := by
    change (if h':h+1≤h+1 then _ else _)=_
    rw [dif_pos le_rfl];rfl
  obtain ⟨D,hd⟩:=lift_entries T ht (boundary Q T h μ ν) (fun v w k=> by
    simp_rw [top]
    exact WilsonPhysicalExteriorGradeCoefficient.regular ht Q s μ (owner (Land.read v)) (Land.read w) k rfl)
  let K:=(changed reads (h+1) h μ ν).submatrix Land.read id
  let L:=(receiver reads (h+1) h ν).submatrix Land.read id
  have hk:K.map f=gather (l:=atTop) (inner R Q T h μ ν) := by
    apply Matrix.ext;intro a b;exact changed_entry reads (h+1) h μ ν (Land.read a) b
  have hl:L.map f=gather (l:=atTop) (edge R Q T h ν) := by
    apply Matrix.ext;intro a b;exact receiver_entry reads (h+1) h ν (Land.read a) b
  let X:=gather (l:=atTop) (lower Q T h μ ν)
  have hx:L.map f=(X*A.map f+(D*K).map f)*U.transpose.map f:=by
    rw [hl,edge_germ,←ha,←hu,←hd,←hk,Matrix.map_mul];rfl
  obtain ⟨Y,hy⟩:=MSGradedReceiverRigidity.rectangle f U A C hL (physical reads V hp h ν)
    (WilsonPhysicalExteriorReceivedGerms.original reads V hp h μ ν) D K L X hx
  intro v a k
  apply (member ht _).mp
  have ent:=congrArg (PowerSeries.coeff k) (congrFun (congrFun hy v) a)
  change coeff k (diagram atTop (fun i=>lower Q T h μ ν i v a))=
    coeff k (PowerSeries.map (ring ht).subtype (Y v a)) at ent
  rw [MSMeasuredGermSeries.coefficient,PowerSeries.coeff_map] at ent
  change hom atTop (fun i=>coeff k (lower Q T h μ ν i v a))∈ring ht
  rw [ent];exact (coeff k (Y v a)).property

end YM.Integration.WilsonPhysicalExteriorSolvedGrade
end
