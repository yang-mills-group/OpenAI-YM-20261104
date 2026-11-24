import YM.OPE.Levy.Path

/-!
# Exact plane comparison on separately measured stations

Use `OPE.Columns.limit_cap` (cutoff/continuum e-plane) with the quantitative
entrance receipts, for arbitrary sublimits at fixed i. No fitted detector
assumptions on this plane. The clocks of both inputs can feed a single
later extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Next.UVStress
open Bid Dash Next.Extract Push.RelayDifference Spec
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{V U:DiffPlan S} {M A R}
variable {X u D m} (a:TableTickets C X u D)(H:Base C f A M R S V) (h:U.Inclusions S) (hg:G.Simple)
      {p:ℕ→Wheel C m}(hp:Lodged f p)
set_option quotPrecheck false
local notation "t" => fun i=> (p i).toStation
local notation "T₀" => rents p

-- avoid ambiguous coercions from `Fin`'s truncated subtraction
def planeAt {d:ℕ} : ∀ i : ℕ, i≤d→Submodule ℂ (S.Field d)
 | 0, _ => ⊥
 | i+1,h => LinearMap.range (U.rise ((Nat.le_add_right i 1).trans h))
def plane {d:ℕ} (e:Fin (d+1)):Submodule ℂ (S.Field d):= planeAt (U:=U) e.val (Nat.le_of_lt_succ e.isLt)
def fits (d:Fin (m+1))(i:ℕ)(b:Filter Cutoffs)(x:(Bel C.book).Field d)(z:C.label d):= Tendsto (fun j=> (t i).atCut j d x) b (𝓝 z)

def weightFit (F:Order) (A:DiffPlan S) (Q':Next.UVStress.Station C m)(d:Fin (m+1))(e:Fin (d.val+1))(r:ℝ) :=
   ∀ (b:Filter Cutoffs) [b.NeBot], b ≤ F.fuse → ∀ (x z), Tendsto (fun j=>Q'.atCut j d x) b (𝓝 z) →
        ∃ y∈plane (U:=A) e, ‖S.project d z-y‖ ≤ r*‖x‖

include a h H hp hg
lemma impact (d:Fin (m+1))(e:Fin (d.val+1))(r:ℝ)(hr:0<r):∀ᶠ i in atTop, weightFit f U ((p i).toStation) d e (Real.exp ((r-e.val)*T₀ i)) :=by
    obtain ⟨k,c,ht,ht',hk,hc,hq,hr'⟩:=hp
    let P:=LinearMap.toContinuousLinearMap (S.project d)
    rcases he: e.val with _|j
    · let o(i:ℕ):= Columns.juice C.path.levels (k i) * (C.S.a (C.ref d) / C.S.a (k i))^d.val
      have h₁:= Columns.rescale (MergeProof.Ribbons.Note.note_a C.S) hk ht'
      have h₂:= Columns.juice_rate_seq C hk ht'
      have hz: RateLE atTop T₀ (fun i=> ‖P‖*(o i*c d i)) 0:= by
         have hs := h₂.mul (((RateIs.const ht (C.S.a_pos (C.ref d))).div h₁).power d)
         have he:= (RateLE.const ‖P‖ ht).mul ((hs.pays ht).mul (hc d))
         simp only [zero_add, mul_one, zero_sub,neg_neg,add_neg_cancel] at he; exact he
      filter_upwards [hz r hr] with i hi b hb hbf x z hT
      let r':= fun (j:Cutoffs)=>quota C d (k i) j.1 j.2 ((t i).atCut j d x)
      have hv: ∀ᶠ j in b, r' j ≤ c d i * ‖x‖ := ((hq d i).filter_mono hbf).mono (fun j hj=>hj x)
      have heq:= (cutoff_grows f).eventually_ge_atTop (k i) |>.filter_mono hbf
      have he0: ‖z‖ ≤ o i * c d i * ‖x‖ :=by
        apply le_of_tendsto hT.norm
        filter_upwards [hv,heq] with j hj hj'
        rw [mul_assoc]; apply le_trans (Columns.whole_origin H _ (hr' d i) hj') (mul_le_mul_of_nonneg_left hj _)
        exact mul_nonneg (zero_le_one.trans (Columns.juice_pos ..)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)
      refine ⟨0,zero_mem _,?_⟩
      rw [sub_zero,Nat.cast_zero,sub_zero]
      refine (P.le_opNorm z).trans ((mul_le_mul_of_nonneg_left he0 (norm_nonneg _)).trans ?_)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans hi) (norm_nonneg x)
    let P₀(i):=Columns.fare C (k i) d j
    have hc':RateLE atTop T₀ (fun i=>‖P‖*(P₀ i*c d i)) (-(e.val:ℝ)):=by
       have hf:= (Columns.fare_rate (v:=k) a hk ht ht' (d:=d) (e:=j)).pays ht
       have h':=(RateLE.const ‖P‖ ht).mul (hf.mul (hc d))
       convert h' using 0
       rw [he]; have hj:j+1 ≤ d.val := by grind
       push_cast [Nat.cast_sub hj]; ring_nf; rfl
    filter_upwards [hc' (r-e.val) (by linarith)] with i hi b hb hbf x z hT
    have he':j<d.val:=by grind
    let y₀:Rowe C d:= fun j=>(t i).atCut j d x
    obtain ⟨y,hy,hz⟩ := Columns.limit_cap a hg H h he' y₀ z hbf (hr' _ _) (((hq d i).filter_mono hbf).mono fun j hj=>hj x) hT
    refine ⟨S.project d y,?_,?_⟩
    · unfold plane
      have ht' {j i :ℕ}(hj':j≤d.val)(hi':i≤d.val)(he':j=i):planeAt (U:=U) j hj'=planeAt (U:=U) i hi':=by subst i; rfl
      rw [ht' _ (by grind) he]; exact hy
    rw [←map_sub,←he]; refine (P.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans ?_)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans hi) (norm_nonneg x)

end YM.OPE.Levy
