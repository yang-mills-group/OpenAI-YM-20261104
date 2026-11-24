import YM.Integration.WilsonViewerReportingGrid
import YM.Integration.WilsonViewerAlignedResidual
import YM.OPE.Cards.Pressure

/-! The original selected Wilson field at a screened aligned site. The raw
label maps are chosen once per grade at that radius, before varying sites. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonViewerGridPins
open Function Filter Set RG Lattice Wilson Extraction Table Spec OPE OPE.Orbits PhysMS Trace.Pilot
open GapsContact.Ascent GapsContact.Seams PhysicalNext.Repeat.Legato
open WilsonViewerReportingGrid WilsonViewerAlignedResidual WilsonAddressedReportingScale
open scoped Classical Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {ℓ:Ultrafilter (ℕ×ℕ)} {H:ℕ} {g:ℝ→ℝ}
local notation "C₀" => R.family

structure Maps (C:Family G) (T:Table C.book) (H:ℕ) where
  limit : (i:Fin (H+1)) → T.Field i →ₗ[ℂ] C.label i
  field : (i:Fin (H+1)) → (ℕ×ℕ) → T.Field i →ₗ[ℂ] C.label i

instance : Inhabited (Maps (C₀) S H) := ⟨⟨fun _=>0, fun _ _=>0⟩⟩

def Lives (Γ:Grid (ℓ:=ℓ) F H g) (r:ℝ) (E:Maps (C₀) S H) : Prop :=
  ∀ (d:Fin (H+1)) (v:S.Field d),
    S.project d (E.limit d v)=v ∧
    Tendsto (fun u=>E.field d u v) (ℓ:Filter (ℕ×ℕ)) (𝓝 (E.limit d v)) ∧
    (∀ N p, Γ.date r<N → Next.UVStress.quota (C₀) d (Γ.date r) N p (E.field d (N,p) v) ≤
      (C₀).S.a (Γ.date r)^d.val*dock (radius Γ.stage r)^Γ.stage*cost F d (radius Γ.stage r) v) ∧
    ∀ᶠ u:ℕ×ℕ in f.fuse, Cards.PaidAt (C₀).S u.1 u.2 (Γ.width r) ((C₀).beta u.1 u.2)
      (dock (radius Γ.stage r)^Γ.stage*cost F d (radius Γ.stage r) v) ((C₀).O u.1 u.2 (E.field d u v) 0)

theorem portfolio (Γ:Grid (ℓ:=ℓ) F H g) :
    ∃ E:ℝ→Maps (C₀) S H, ∀ᶠ r in trail, Lives Γ r (E r) := by
  classical
  refine ⟨fun r=>Classical.epsilon (Lives Γ r),Γ.plots.mono fun r submitted=>Classical.epsilon_spec ?_⟩
  choose b w back converges paid using fun d:Fin (H+1)=>labels F (submitted.budget d (Nat.le_of_lt_succ d.isLt))
  exact ⟨⟨b,w⟩, fun d v=>⟨back d v,converges d v,paid d v⟩⟩

/-- These are the genuine unconditioned ordinary moments at the embedded
microscopic addresses on the caller's actual periods and upper cutoffs. -/
def atCut {n:ℕ} (d:Caps n) (s:ℕ) (o:Fin n → Cover) (Y:(ℕ×ℕ) → (C₀).book.Vector d)
    (i:ℕ×ℕ):ℂ := (C₀).ensemble d (fun a=>Cells.location (C₀).S s i.1 i.2 (o a)) (Y i)

theorem limit {n:ℕ} {d:Caps n} (Γ:Grid (ℓ:=ℓ) F H g) {r:ℝ} (rp:0<r) {E:Maps (C₀) S H}
    (lives:Lives Γ r E) (chosen:(ℓ:Filter (ℕ×ℕ))≤f.fuse) (P:tower S) (v:MaxwellSlots (C₀) d)
    (within:∀i,d i≤H) {W:Finset E4} {o:Fin n → Cover} {y:Points n} (pin:Pin (C₀).S W r (Γ.date r) o y) :
    let index (i:Fin n):Fin (H+1):=⟨d i,Nat.lt_succ_of_le (within i)⟩
    let Y:=fun u i=>E.field (index i) u (P (d i) (v i))
    Tendsto (atCut (R:=R) d (Γ.date r) o Y) (ℓ:Filter (ℕ×ℕ)) (𝓝 (measured F none P v r y)) := by
  intro index Y
  let b:= fun i=>E.limit (index i) (P (d i) (v i))
  have placed:Extraction.Order.grid (C₀) (Γ.date r) o=r • y := by
    ext i a
    exact congrArg (fun x:E4=>x a) (pin.placed i).symm
  have genericSite:Extraction.Order.grid (C₀) (Γ.date r) o ∈ generic n := by
    rw [placed]
    intro a i k eq
    apply pin.screened a
    change r*y i a=r*y k a at eq
    exact mul_left_cancel₀ rp.ne' eq
  have exactCut:=Cards.variation (C:=(C₀)) (d:=d) o F.room.generic genericSite b Y
    (fun i=>(lives (index i) (P (d i) (v i))).2.1) chosen
  have net:measured F none P v r y=S.value d (Extraction.Order.grid (C₀) (Γ.date r) o) b := by
    have eq:(fun i=>P (d i) (v i))=fun i=>S.project (d i) (b i):=funext fun i=>(lives (index i) _).1.symm
    change S.classMoment S d (r • y) (fun i=>P (d i) (v i))=_
    rw [eq,←placed]
    exact S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) _ (generic_conf n genericSite) b
  rw [net]
  exact exactCut

/-- At a single actual site, take ordered physical cutoffs on the original
filter first. The independent regulator only needs an arbitrarily late priced reading. -/
theorem compare {n:ℕ} {d:Caps n} (Γ:Grid (ℓ:=ℓ) F H g) {r:ℝ} (rp:0<r) {E:Maps (C₀) S H}
    (lives:Lives Γ r E) (chosen:(ℓ:Filter (ℕ×ℕ))≤f.fuse) (P:tower S) (v:MaxwellSlots (C₀) d)
    (within:∀i,d i≤H) {W:Finset E4} {o:Fin n → Cover} {y:Points n} (pin:Pin (C₀).S W r (Γ.date r) o y)
    {ι:Type*} {l:Filter ι} (bank:ι→ℂ) {value:ℂ} (independent:Tendsto bank l (𝓝 value)) (η:ℝ)
    (signed:∃ᶠ k in l, f.late fun N p=> ‖atCut (R:=R) d (Γ.date r) o
      (fun u i=>E.field ⟨d i,Nat.lt_succ_of_le (within i)⟩ u (P (d i) (v i))) (N,p)-bank k‖≤η) :
    ‖measured F none P v r y-value‖≤η := by
  apply le_of_tendsto_of_frequently ((tendsto_const_nhds (x:=measured F none P v r y)).sub independent).norm
  refine signed.mono fun k physical=>?_ 
  exact le_of_tendsto (((limit Γ rp lives chosen P v within pin).sub_const (bank k)).norm)
    (((f.fused _).2 physical).filter_mono chosen)

end YM.Integration.WilsonViewerGridPins
end
