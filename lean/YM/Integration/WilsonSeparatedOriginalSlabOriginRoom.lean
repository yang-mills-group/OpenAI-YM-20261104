import YM.Integration.WilsonSeparatedOriginalSlabYoungAnchor
import YM.Integration.WilsonReportHarvestSlabShiftSingle

/-! The independent unit insertion at the original reporting origin is compatible with every occupied parent of the whole physical profile. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabOriginRoom
open Filter Finset Lattice Wilson Labels RG Source RG05Readout MergeProof RG05Readout.Many
open WilsonSeparatedOriginalSlabActiveWeights
open scoped Classical BigOperators
variable {G:Gauge}(C:Family G)

theorem aperture (n:ℕ)(degree:3≤C.path.levels.clock.J n):4≤apron C.path.levels n:=by
  have stage:C.path.levels.clock.J n≤C.path.levels.clock.J (n+1):=C.path.levels.fits.mono (Nat.le_succ n)
  have step:0<(C.S.block n).val^4:=pow_pos (C.S.block n).property _
  unfold apron
  exact (show 4≤C.path.levels.clock.J (n+1)+2 by omega).trans (Nat.le_mul_of_pos_right _ step)

theorem original (hG:G.Simple)(pace:∀b:ℕ,((C.S.block b).val:ℝ)≤Real.log (RG16.Lambda C.path.levels b))
    {cap:ℝ}(cp:0≤cap):∀ᶠb:ℕ in atTop,∀r:ℝ,0≤r → r≤C.S.a b → ∀per (o:Fin 3 → Site (C.side (b+1) per)),
      o∈Pulse.area (C:=C) (range C (b+1) r cap) → ∀i,
        coverNumber ((C.path.levels.budget (b+1)).B) ({0,o i}:Support (C.side (b+1) per)) ≤
          Ribbons.peepers C.path.levels (b+1):=by
  filter_upwards [WilsonSeparatedOriginalSlabYoungAnchor.original C hG pace cp] with b paid
  intro r rp room per o inside i
  let y:Fin 3 → Site (C.side (b+1) per):=fun j=>if j=0 then 0 else o i
  have present:y∈Pulse.area («C»:=C) (range C (b+1) r cap):=by
    simp only [Pulse.area,mem_filter,mem_univ,true_and] at inside ⊢
    intro j;by_cases eq:j=0
    · simp [y,eq]
    · simpa only [y,if_neg eq] using inside i
  have reach:=paid r rp room per y present 0 1
  simpa [y] using reach

theorem margin {n:ℕ}{r cap:ℝ}(rp:0<r)(cp:0≤cap)(mesh:C.S.a n≤r):
    2*(C.S.a n*(2*(range C n r cap:ℝ)+1))≤(4*cap+14)*r:=by
  have ap:=C.S.a_pos n
  have pos:0≤(r*cap+2*C.S.a n)/C.S.a n:=by positivity
  have h:(range C n r cap:ℝ)<(r*cap+2*C.S.a n)/C.S.a n+1:=Nat.ceil_lt_add_one pos
  have cover:C.S.a n*(range C n r cap:ℝ)<r*cap+3*C.S.a n:=by
    have p:=mul_lt_mul_of_pos_left h ap
    rw [mul_add,mul_div_cancel₀ _ ap.ne'] at p;linarith
  linarith

end YM.Integration.WilsonSeparatedOriginalSlabOriginRoom
