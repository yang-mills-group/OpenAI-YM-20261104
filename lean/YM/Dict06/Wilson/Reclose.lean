import YM.Dict06.Wilson.Hol
import YM.Next.FOUNDATIONS.JetReads
/-!
The joint engineering/slot projection on the source alphabet,
WITHOUT separate position-test letters (tensor these in separately). Test
on arbitrary real radial jets; by Labels.eval_ext / jet_test_ext this does
not lose any polynomial coordinate. Uses the FULL log of the holonomies in
the positive orientations, and ordinary derivatives divided by factorials.
No quotient by equations; that is a different stage.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.Dict06.Wil
open Series Lattice Wilson Labels Source Source.Drops Topology Function Set Filter
open scoped ContDiff Matrix.Norms.Frobenius BigOperators Classical Topology
open Work.G05 Next.Foundations
variable {G : Gauge} {d:ℕ} {F:Frame G d}

def engineered (J : Jet G) (t:ℝ) : Snap G d := trunk d (scaleJet J t)
lemma engineered_diff (J : Jet G) : ContDiff ℝ ω (engineered (d:=d) J) :=
  by
  have he {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (e:E) (j:ℕ): ContDiff ℝ ω (fun t:ℝ=> t^j • e) := (contDiff_id.pow j).smul contDiff_const
  exact contDiff_pi.mpr fun i => he _ _
@[simp] lemma engineered_zero (J:Jet G): engineered (d:=d) J 0=0:=by
  funext i; simp [engineered,trunk,scaleJet]
lemma engineered_amplitude (J:Jet G)(t a:ℝ):engineered (d:=d) (t • J) a=t • engineered J a:=by
  ext1 i; simp [engineered,trunk,scaleJet];rw [smul_comm]

lemma on_scale (H:Hol G) (S:SectionData F) (c:F.Coeff) (J:Jet G):
    (echo S c ∘ logTest H d S.stencil) ∘ engineered J =ᶠ[𝓝 0]
      fun t=> S.evaluate c (H.links d J t) := by
  have h : Tendsto (engineered (d:=d) J) (𝓝 0) (𝓝 0) := by
    rw [← engineered_zero J]; exact (engineered_diff J).continuous.tendsto (0:ℝ) -- rewrite also domain?
  filter_upwards [h.eventually (section_links S H c)] with t ht
  rw [Function.comp_apply,ht, Drops.scales H J]; rfl

/-- The `(m,l)` engineering/slot Taylor test of f on Snap at all real
radial data J. First project the unscaled Snap amplitude to l; then take
engineering m. -/
def probe (f:Snap G d→ℂ) (m l:ℕ) (J:Jet G) := ordinary m (term f l ∘ engineered J)

lemma test_scale {f:Snap G d→ℂ} (m : ℕ) (hm:m≤d) (hf:ContDiffAt ℝ d f 0) (J:Jet G):
    ordinary m (f ∘ engineered J) = ∑ l∈Finset.range (d+1), probe f m l J := by
  let Q:=engineered (d:=d) J
  have hz :Q 0=0:=engineered_zero _
  have he := jets_comp (f:=Q) (f':=Q) (engineered_diff J|>.contDiffAt.of_le (m:=(d:ℕ)) le_top) (engineered_diff J|>.contDiffAt.of_le le_top)
           (g:=f) (g':=blockTaylor d f) (show ContDiffAt ℝ d f (Q 0) from by rw [hz]; exact hf) (blockTaylor_contDiff d f _|>.contDiffAt)
           rfl (fun _ _=>rfl) (fun i hi=>by rw [hz,blockTaylor_jets hf i hi]) m hm
  have H : ordinary m (f ∘ Q) = ordinary m (blockTaylor d f ∘ Q):= congrArg (fun P:Tensor.T ℝ ℂ m => (m.factorial:ℝ)⁻¹ • P 1) he
  rw [H, show blockTaylor d f ∘ Q = fun t=>∑ l∈Finset.range (d+1),(term f l ∘ Q) t from funext (fun y=>Finset.sum_apply (Q y) (Finset.range (d+1)) (term f)),
    ordinary_sum (Finset.range (d+1)) (fun l=>term f l ∘ Q) m (fun l _=> ((Tensor.diag_smooth _ _).comp (engineered_diff J|>.of_le le_top)).contDiffAt)]
  rfl
lemma probe_slot (f:Snap G d→ℂ)(m l:ℕ)(J:Jet G)(t:ℝ) : probe f m l (t•J)=t^l • probe f m l J:=by
  unfold probe term ordinary
  simp_rw [Function.comp_def,engineered_amplitude,Tensor.homogeneous]
  rw [iteratedDeriv_fun_const_smul_field (𝕝:=ℝ)]; rw [smul_comm]

lemma tier_pure {p : Label G d} (m : ℕ) (a:ℕ×ℕ) (h:p∈ Grade a):
    tier m p.val = if m=a.1 then p.val else 0 := by
  have hh : MvPolynomial.IsWeightedHomogeneous Labels.generation p.val a.1 := by
    intro i hi
    change height i = a.1
    exact (congrArg Prod.fst (weight_slot i)).symm.trans (congrArg Prod.fst ((pure_grade a p).mp h hi))
  split_ifs with hc
  · subst m; exact hh.weightedHomogeneousComponent_same
  exact hh.weightedHomogeneousComponent_ne m hc
lemma slot_le (i:F.Index) : (F.grades i).2≤d := by
  by_contra! h
  apply F.basis.ne_zero i
  apply Subtype.ext
  change (F.basis i).val = (0:Pol G)
  ext m
  by_cases hz : MvPolynomial.coeff m (F.basis i).val=0
  · simp [hz]
  have hm := Labels.power_le m; have hx := (pure_grade _ _).mp (F.pure i) hz
  have hv : height m ≤ d:= (MvPolynomial.mem_restrictSupport_iff ℂ).mp
    (show (F.basis i).val∈limited G d from (F.basis i).property.1)
    (MvPolynomial.mem_support_iff.mpr hz)
  rw [hx] at hm
  omega

variable (H:Hol G) (S:SectionData F)
def snapped (c:F.Coeff) : Snap G d → ℂ := echo S c ∘ logTest H d S.stencil
lemma snapped_diff (c:F.Coeff) : ContDiffAt ℝ ω (snapped H S c) 0 :=
   (echo_smooth S c).contDiffAt.comp _ (chart_of_links H d S.stencil).1
variable (hs:S.Sound H)
include hs
theorem projecting (i:F.Index) {m l:ℕ}(hm:m≤d)(hl:l≤d) (J:Jet G):
    probe (snapped H S (Pi.single i 1)) m l J=
        (if l=(F.grades i).2 then
           if m=(F.grades i).1 then read J (F.basis i).val
           else 0
         else 0):=by
  let p:=F.basis i; let n:=(F.grades i).1; let k:=(F.grades i).2
  let W:=snapped H S (Pi.single i 1)
  let out(lp:ℕ):=probe W m lp J
  let head:ℂ:=if m=n then read J p.val else 0
  change out l=if l=k then head else 0
  have he (t:ℝ):∑ j∈Finset.range (d+1),t^j • out j = t^k • head:=by
    obtain ⟨_,_,h⟩:=hs.projects (Pi.single i 1) (t•J)
    rw [← F.coords_basis,F.coords.symm_apply_apply] at h
    have hp : iteratedDeriv m (fun h=> S.evaluate (Pi.single i 1) (H.links d (t • J) h)) 0 =
        iteratedDeriv m (fun x=> read (scaleJet (t•J) x) p.val) 0 := by
      simpa only [F.coords_basis] using h m hm
    have hg:W ∘ engineered (t • J)=ᶠ[𝓝 0] _ := on_scale H S _ _
    calc
      _ = ∑ j∈Finset.range (d+1),probe W m j (t • J) := by unfold out; simp_rw [←probe_slot W]
      _ = ordinary m (W ∘ engineered (t • J)) := by rw [test_scale m hm (show ContDiffAt ℝ d W 0 from (snapped_diff H S (Pi.single i 1)).of_le le_top)]
      _ = ordinary m (fun y=>read (scaleJet (t•J) y) p.val) := by rw [ordinary_eq_of_eventual m hg]; unfold ordinary; rw [hp]
      _ = _ := by
        unfold ordinary; rw [deriv_read,smul_smul,inv_mul_cancel₀ (show (m.factorial:ℝ)≠0 by positivity), one_smul,tier_pure m _ (F.pure i)]; unfold head n
        split_ifs
        · exact read_pure J (F.pure i) _
        simp
  rw [← show ordinary l (fun t:ℝ=>t^k • head) = if l=k then head else 0 from monomial ..,← funext he,lookup, if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))]
end YM.Dict06.Wil
