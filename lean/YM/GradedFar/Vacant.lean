import YM.GradedFar.Screen
/-!
# Truth with empty Far experiment from the (G.9) RoundPoint hypothesis

Here buy a fixed T in the range. Use on all fixed-compact questions. Note that this includes everything
needed on **all viewers** of the same two-field test in determining the physical reflection Gram.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2 FVA2.O.Enh FVA2.GradedFar FVA2.Scale FVA2.O.Score
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
    (F: Final C fo S)(J:ℝ→tower S) (hG:G.Simple)
    {n p l h:ℕ} {d: Fin n→ℕ} {K:Set (Points n)}(hx: K⊆conf n)

/-- Exact physical entire reading in the H frame (in compact shape units) -/
def TrueCompact (v:Viewers F)(r:ℝ)(o:E4) (x:Points n) (u:Inputs G d):ℂ :=
    Orbits.moment (spectator F v) (sites o r x) (labels J r u)
/-- Exact formal entire reading in position convention (no scale change) in compact shape units. -/
def FormalCompact (A:Arenas G)(l:ℕ) (hd:Through l d) (x:Stage n)(u:Inputs G d) :=
    PowerSeries.mk (fun k=>A l n x k (raised hd u))
-- proper empty identities
abbrev nofar : Fin 0→ℕ:=Fin.elim0
abbrev nofare (l:ℕ): Through l nofar := fun i=>Fin.elim0 i
abbrev nowhere (G:Gauge): Inputs G nofar:= fun i=> Fin.elim0 i
lemma nofar_ok : (0:Points 0)∈Outside 0:= (fun _ _ _=>@Subsingleton.elim (Fin 1) _ _ _) -- injective 1
lemma nofar_unit : Box (nowhere G) 1:=fun i=>Fin.elim0 i
lemma true_nofar (v:Viewers F)(r T:ℝ)(o:E4)(x:Points n)(u:Inputs G d)(hp:0<r)(hx:x∈conf n):
    today F J v o r (r*T) r x 0 u (nowhere G)= TrueCompact F J v r o x u := by
  rw [today_apply,whole_observed,TrueCompact,Orbits.observed]
  have hh: Injective (sites o r x):= fun i j h=>hx (smul_right_injective E4 hp.ne' (add_left_cancel (show o+_=o+_ from h)))
  let V : Fin n→E4 := sites o r x
  exact (Fork.renameRead (Equiv.sumEmpty (Fin n) (Fin 0)).symm (z:=beside V (sites o (r*T) (0:Points 0)))
    (spectate F v).laws.toSymmetric hh (funext fun _=>rfl) (funext fun _=>rfl)).symm
lemma formal_nofar (A:Arenas G)(x:Stage n)(hd:Through l d)(u:Inputs G d)(η t:ℝ) : constantCrop A η hd
    (nofare l) x.val 0 p t u (nowhere G)= crop p t (FormalCompact A l hd x u):=by
  rw [constantCrop,bothCrop_apply]; apply congrArg; ext1 k; simp only [PowerSeries.coeff_mk, FormalCompact]
  have hb:forest x.val (squeeze η (0:Points 0))=x.val:=by
    ext1 i; rw [show i=Fin.castAdd 0 i from Fin.ext rfl, forest_left]; exact rfl
  rw [hb,rawCoeff_apply _ _ _ _ _ _ _ x.property]
  apply congrArg (A l n x k); funext i
  exact Fin.append_left ..

local notation "g" => strength G
variable (t:ℝ→ℝ)(A:Arenas G) (p : ℕ) (hd:Through l d)
    {Λ B:ℝ}(hΛ:0<Λ)(hB:0<B) (hf:RoundPoint F J t A hd (nofare l) Λ B p K {0})
include hG hx hΛ hB hf
theorem compact_price :∃ C:ℝ,0≤ C ∧ ∀ᶠ r in trail,∀ v o x,∀ h: (x:Points n) ∈ K,∀ u, Box u 1 →
    ‖TrueCompact F J v r o x u-crop p (t r) (FormalCompact A l hd ⟨x,hx h⟩ u)‖ ≤ C*(g r)^(p+1) := by
  obtain ⟨M,hM,j,T₀,hT₀,h⟩:=hf
  let c:= (1+Real.log T₀)^j; have hT:1≤T₀:=by linarith
  have ht:0 ≤ c:=pow_nonneg (by linarith [Real.log_nonneg hT]) _
  refine ⟨M*c,mul_nonneg hM ht,?_⟩
  have hi:∀ᶠ r in trail, T₀ ≤ Λ*(g r)^(-B) := ((strength_falls hG).eventually (Budget.upwards hB hΛ T₀)).mono fun _ h=> h _ le_rfl
  filter_upwards [h,hi,self_mem_nhdsWithin] with r ha hr (hp:0<r) v o x he u hu
  specialize ha T₀ le_rfl hr x he 0 (Set.mem_singleton _) o v u (nowhere G) hu nofar_unit
  rw [true_nofar _ _ _ _ _ _ _ _ hp (hx he), (show constantCrop A _ hd (nofare l) _ 0 p _ u (nowhere G)=_ from
      formal_nofar A ⟨x,hx he⟩ hd u (-Real.log T₀) (t r))] at ha
  exact ha.trans_eq (by ring)
end YM.Integration.GradedFar
