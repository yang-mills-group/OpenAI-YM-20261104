import YM.RG12.Kintsugi.Mantle
/-! # Partial physical transfer endpoints written in ticket language -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi
open Filter Function Set Finset Analysis Extraction Lattice RG Org Spec Next.UVStress Climb Table Real UVNext.FreeStress OPE
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Alidade.Route P lit U.room.cutoff) (hs:Ranked P)
variable (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤f.fuse)(hG:G.Simple)(H:OPE.Facilities C f S)
local notation "χ"=>C.path.levels.clock.hatBeta

def towards (l:Filter (ℕ×ℕ))(x:C.label 4) : Prop:=∃ p:ℕ,∀ᶠ k in atTop,∃ (v:C.label 4)(q:ℕ×ℕ→ C.label 4), S.project 4 v=S.project 4 x ∧ Tendsto q l (𝓝 v) ∧ ∀ᶠ i in l,quota C 4 k i.1 i.2 (q i) ≤ χ k^p
-- outlet assertion on specified limits x in some sector, whole by default.
def outSector (g:Filter (ℕ×ℕ))(d w:ℕ)(L:S.Field d→ₗ[ℂ]ℂ)(P:S.Field d→Prop:=fun _=>True):Prop:=
    ∃ p:ℕ,∀ᶠ k in atTop,∀ (l:Filter (ℕ×ℕ)) [l.NeBot],l≤g→∀(x:C.label d)(u:ℕ×ℕ→C.label d)(r:ℝ),
     (∀ᶠ i in l,quota C d k i.1 i.2 (u i) ≤ r)→ Tendsto u l (𝓝 x)→ P (S.project d x) → ‖L (S.project d x)‖ ≤ χ k ^p/C.S.a k^(d-w)*r
structure Bearing (l:Filter (ℕ×ℕ)) : Prop where
    inlet (x:C.label 4): S.project 4 x∈GrainSpace U→ towards (S:=S) l x
    peal {L:Auspect S} : Peal U.room.kernel.spin L→∀ i j:Axis,outSector l 4 4 (L i j).toLinearMap
    hull (L:S.Field 4→ₗ[ℂ]ℂ): outSector l 4 4 L (· ∈ GrainSpace U)
    caught : GrainSpace U≠⊥∧∃ L:Auspect S,Peal U.room.kernel.spin L ∧ ∀ x, x∈GrainSpace U→(∀ i j:Axis,L i j x=0)→x=0
    centered i j : ∀ᶠ k in atTop,∃ (v:C.label 4)(q:ℕ×ℕ→ C.label 4), S.project 4 v=reCenter S U.sector.energy i j ∧ Tendsto q l (𝓝 v) ∧ ∀ᶠ i in l,quota C 4 k i.1 i.2 (q i) ≤ C.path.levels.clock.hatBeta k^10
    rest (d w:ℕ)(hw:w≤d)(L:S.Field d→ₗ[ℂ]ℂ) : w < 4 →
      (∀ e:ℕ,∀ he:e<w,∀ x:S.Field e,L (U.sector.derivatives.rise (he.le.trans hw) x)=0) → outSector l d w L

include h he hf hG H hs
lemma ships : Bearing U ϕ:=by
   have hu(k:ℕ) : 0 ≤ χ k:=zero_le_one.trans (C.path.levels.fits.delayed k).le
   have heq (d w:ℕ)(L:S.Field d→ₗ[ℂ]ℂ)(G:S.Field d→Prop)(p:ℕ)(hp:∀ᶠ k in atTop,∀ v:C.label d,G (S.project d (M d k v))→ ‖L (S.project d (M d k v))‖≤ χ k ^ p / C.S.a k^(d-w)*mass C d v):outSector ϕ d w L G:=by
      refine ⟨p,?_⟩
      filter_upwards [hp,eventually_ge_atTop (C.ref d)] with k hk ht l hB hL x u r hx hv hX
      obtain ⟨v,rfl,hLx⟩:= he.value d k ht hL u x r hx hv
      exact (hk _ hX).trans (mul_le_mul_of_nonneg_left hLx (div_nonneg (pow_nonneg (hu _) _) (pow_nonneg (C.S.a_pos _).le _)))
   obtain ⟨W,hW⟩:=kiln U hG
   refine ⟨?_,?_,?_,⟨nonvacancy U M P h hs he hf hG H,heated U W hW⟩,?_,?_⟩
   · intro x hx; obtain ⟨p,hp⟩:=hull_in U M P h hs he hf hG H _ hx
     exact ⟨p,(hp.and (eventually_ge_atTop (C.ref 4))).mono fun k hk=> (he.characterize S 4 k hk.2 (l:=ϕ) le_rfl _ _).2 hk.1⟩
   · intro L hL i j
     refine heq 4 4 (L i j).toLinearMap (fun _=> True) 10 ((sectors_ship U M P h.free hs hG H he hf hL).mono fun _ hi z _=>?_)
     exact hi i j z
   · intro L; obtain ⟨p,hp⟩:= hull_out U M P h hs he hf hG H L
     exact heq _ _ L (·∈GrainSpace U) p (by simpa using hp)
   · intro i j; filter_upwards [cent_in U M P h.free hs H he hf hG i j,eventually_ge_atTop (C.ref 4)] with k hk hk'
     exact (he.characterize S 4 k hk' (l:=ϕ) le_rfl _ _).2 hk
   intro d w hw L ht hr
   obtain ⟨p,hp⟩:= Spot.earned_low U M P h he hf hG H d w ht L hw hr
   exact heq d w L _ p (hp.mono fun _k hk v _=> hk v)
end YM.RG12.Kintsugi
