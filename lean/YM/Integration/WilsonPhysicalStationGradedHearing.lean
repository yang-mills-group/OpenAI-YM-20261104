import YM.Integration.WilsonPhysicalStationGradedVoter
import YM.Integration.WilsonPhysicalStationElectedEars

/-! Each graded part of the original vote has its own measured ordinary response on the same two filed arms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationGradedHearing
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Further.CorrectedLift
open WilsonPhysicalStationGradedVoter (Bank portion)
open WilsonPhysicalStationThermalPair (raw)
open WilsonPhysicalStationTableJump (pair)
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonPhysicalStationSubtractedPosts (heard)
open WilsonMovingForkReporterBothArms (Filed)
open scoped Topology Classical BigOperators Matrix

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{H:(Bel R.family.book).Hierarchy}
    {ℓ:Ultrafilter (ℕ×ℕ)}{D:ℕ}(B:Vane R.family D){h:ℕ}(db:h<D+1)(cb:B.checked f H D)
    {N per:ℕ}(top:B.k<N)(P:ℕ×ℕ→Prop)
    (w:Bank R.family h P→(ℕ×ℕ)→R.family.label h)(u:(standard R.family).Field h)

def column (j:ℕ)(o:Fin 2 → Cover)(peer:R.family.label h)(i:Bank R.family h P):ℂ:=
  pair R ⟨h,db⟩ N per j o (raw R B ⟨h,db⟩ (p:=per) cb top (Pi.single i.val 1)-
    (R.family.factory h N per).terminal (w i (N,per))) peer

theorem finite (j:ℕ)(o:Fin 2 → Cover)(peer:R.family.label h):
    pair R ⟨h,db⟩ N per j o (B.wheel.atCut (N,per) ⟨h,db⟩ (portion R.family h P u)-
        lower R (fun i:Bank R.family h P=>ladder R.family h u i.val) w (N,per)) peer=
      ∑i:Bank R.family h P,ladder R.family h u i.val*column R B db (per:=per) cb top P w j o peer i:=by
  let M:=R.family.ensemble (N:=N) (p:=per) (fun _:Fin 2=>h) (fun i=>location R.family.S j N per (o i))
  let L:R.family.label h→ₗ[ℂ]ℂ:=M.toLinearMap ![0,peer] 0
  have applied (y:R.family.label h):L y=pair R ⟨h,db⟩ N per j o y peer:=by
    change M (Function.update ![0,peer] 0 y)=M ![y,peer]
    exact congrArg _ (funext fun i=>by fin_cases i <;>simp [Function.update])
  rw [←applied,WilsonPhysicalStationGradedVoter.original R B db cb top P u]
  unfold lower
  rw [←Finset.sum_sub_distrib]
  simp only [←smul_sub]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  simp only [applied,column]

variable (F:Final R.family f S)(J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
    {m k:ℕ}(hm:h ≤ m)(hk:h ≤ k)(issued:(V k).checked f H k)

def posted (z:(standard R.family).Field h)(j:ℕ)(o:Fin 2 → Cover)(p:ℕ×ℕ):ℂ:=
  if top:(V k).k<p.1 then
    ∑i:Bank R.family h P,ladder R.family h u i.val*column R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) issued top
      P w j o ((V m).wheel.atCut p ⟨h,Nat.lt_succ_of_le hm⟩ z) i
  else 0

include F in
theorem original (simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    {am bm ak bk:ℝ}(left:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)(right:Filed (f:=f) (l:=ℓ) J₀ J V h m am bm)
    (v:Bank R.family h P→R.family.label h)
    (limits:∀i,Tendsto (fun p:ℕ×ℕ=>(R.family.factory h p.1 p.2).terminal (w i p)) (ℓ:Filter _) (𝓝 (v i)))
    (z:(standard R.family).Field h)(j:ℕ)(o:Fin 2 → Cover)(safe:Extraction.Order.grid R.family j o∈conf 2):
    Tendsto (posted R P w u V hm hk issued z j o) (ℓ:Filter _)
      (𝓝 (S.classMoment S (fun _:Fin 2=>h) (Extraction.Order.grid R.family j o)
        ![J.U k h (portion R.family h P u)-S.project h (∑i:Bank R.family h P,ladder R.family h u i.val • v i),
          J.U m h z])):=by
  apply (WilsonPhysicalStationSubtractedPosts.voted R F J₀ J V hm hk simple below left right
    (fun i:Bank R.family h P=>ladder R.family h u i.val) w v limits (portion R.family h P u) z j o safe).congr'
  filter_upwards [WilsonPhysicalStationElectedEars.ready below (V k).k] with p gate
  unfold posted
  rw [dif_pos gate]
  exact finite R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) issued gate P w u j o _

end YM.Integration.WilsonPhysicalStationGradedHearing
end
