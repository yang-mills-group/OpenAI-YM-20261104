import YM.RGLocalTaylor.Mayer.Earning
import YM.RG01.Survive.Coupled
/-!
# Actual quantitative producer of an RG01 `LeafReady`

No low-cluster/arity/depth restriction in the underlying `Prepared`. It uses
effective-interaction Taylor moments BEFORE any insertion of patch kernels on
the lifted gauge algebra, i.e. real measured log components, on *all* true
paths, including every initialized/refreshed E and hard/error entry in the
pushed density. Real budgets on derivatives at fixes (every V on Healthy), and
qualitative off-healthy/read-scope compatibility are supplied. No positive mark
insertions in this receipt. `Ready` for the second tree pass included.

Use-ready on the actual Fare agenda via the delay strengthening. Analytic
derivatives in `BudgetPoint`, etc, require also the physical horizon charges;
never assume a price in a later presentation just from the exact identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open Trees RG01.Survive
namespace Mayer
variable {ρ discount θ K α uJ vJ e : ℝ} {M : ℕ} {p : Molecule S} {N : Captain H j C' d v Y A b r B q n χ}

-- last slot index M+1, includes the true error (zero formulas outside scan only prior to this setting).
def issue (H : Cash W s μ L Q o C T R) (χ : Chi) (M : ℕ) : Expansions H M := fun i p =>
    if p.val=M+1 then excess H i.val χ M else atLeaf H i.val χ M p.val

lemma fullIdentity (H : Cash W s μ L Q o C T R) (i:H.ThinP) : (∑ m:Orders M,issue H χ M i m)=fun V=>leaflet H χ V i := by
  let f m:=atLeaf H i.val χ M m
  have h₁ (m:Fin (M+1)): issue H χ M i m.castSucc=f m.val := if_neg (ne_of_lt m.isLt)
  rw [Fin.sum_univ_castSucc,show issue H χ M i (Fin.last (M+1))=_ from (show _=excess H i.val χ M from if_pos (Fin.val_last ..))]
  simp_rw [h₁,excess]; rw [add_sub_cancel]; exact funext fun i=> Insert.nativeRender ..

lemma fullTerm (k : ℕ) (H : Cash W s μ L Q o C T R) (i : Molecule S) (χ : Chi) (m : ℕ):
    let F := atLeaf H i χ k m; GaugeInvariant F ∧ Measurable F ∧ LocalOn (H.unionP i) F := by
  dsimp only; unfold atLeaf; split
  swap; · exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
  let f (u:Decors i k) := Mayer.tagged H i (leg H (own i)) u
  have ht u : Fits H (f u) (H.unionP i) 1:= fits_tagged (f':=leg H (own i)) _ (by simp) _
  refine ⟨?_,?_,?_⟩
  · intro x U; exact Finset.sum_congr rfl fun u _=> (f u).onLog_invariant (H:=H) (χ:=χ) i x U
  · exact Finset.measurable_fun_sum _ (fun u _=> ((ht u).log_seam (χ:=χ)).2)
  intro U V hu
  exact Finset.sum_congr rfl fun u _=> ((ht u).log_seam (χ:=χ)).1 U V hu
lemma fullShape (k : ℕ) (H : Cash W s μ L Q o C T R) (χ : Chi) (i:H.ThinP) (p : Orders k) :
    let F := issue H χ k i p; GaugeInvariant F ∧ Measurable F ∧ LocalOn (H.smallAt i) F := by
  dsimp only; unfold issue; split
  · let Y:=native H i.val; let s u:=atLeaf H i.val χ k u
    have hv := (fits_native H i.val 1).log_seam (χ:=χ)
    have ht := fullTerm k H i.val χ
    unfold excess; refine ⟨?_,?_,?_⟩
    · intro z U; simp only [Pi.sub_apply,Finset.sum_apply]; exact congr_arg₂ (·-·) (Y.onLog_invariant (χ:=χ) i.val z U) (sum_congr rfl (fun j _=> (ht j.val).1 z U))
    · apply hv.2.sub
      apply show ((Measurable (fun V=> (∑ d:Fin (k+1),atLeaf H i.val χ k d.val) V))) from ?_
      simp_rw [Finset.sum_apply]
      exact Finset.measurable_fun_sum _ (fun j _=> (ht j.val).2.1)
    intro x y he
    simp only [Pi.sub_apply,Finset.sum_apply]; exact congr_arg₂ (·-·) (hv.1 x y he) (sum_congr rfl (fun j _=> (ht j.val).2.2 x y he))
  exact fullTerm ..

set_option quotPrecheck false
local notation "vₜ" => parentFee Q L μ s uJ θ e ρ α j l M
abbrev prices (N : Captain H j C' d v Y A b r B q n χ) (l M : ℕ) (e uJ θ ρ α : ℝ) (p : Molecule S) (k : Orders M) : ℝ:= (ρ^k.val)⁻¹ * prenex N.conduit l M e uJ θ ρ α p
structure Prepared (N : Captain H j C' d v Y A b r B q n χ) (l M : ℕ) (e uJ θ ρ α a w δ : ℝ) : Prop where
  pos : ∀ p : H.ThinP, ∀ k, 0≤ prices N l M e uJ θ ρ α p.val k
  scale : 1≤ρ
  recognizes (p:H.ThinP) :
    ∑ k:Orders M,prices N l M e uJ θ ρ α p.val k * ρ^k.val ≤ carrier N.conduit l M e uJ θ ρ α p.val
  holds (p:H.ThinP) (t : Orders M) (U : Config G c) : Healthy (Pressure.temp s) (H.smallAt p) U →
    Ore U (issue H χ M p t) v (prices N l M e uJ θ ρ α p.val t) j
  agrees : Trees.Ready H.smallAt (radiusB s) (fun i=>2^j*carrier N.conduit l M e uJ θ ρ α i.val) (a+δ) w δ (1/2)

lemma purchased (h : Awning H N.conduit A b discount e uJ vJ k l) (he : Approved K θ j M) (ht : Q.goal L s ≤ K) (hr:ρ*Q.goal L s≤1)
    (ha: 1≤α) (hz : (M+4:ℝ)*r≤α) (hρ: 1≤ρ)
    (hA : discount ≤ (ρ^(M+1))⁻¹) (hE : Real.exp (- Q.mark L μ s) ≤ (ρ^(M+1))⁻¹)
    (hd : degreePrice (radiusB s) (spreadRate M θ ρ * (Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) vₜ η ≤ 1/2) (hη:0<η) (hq:a+η+η≤ Q.exp) : Prepared N l M e uJ θ ρ α a vₜ η := by
  constructor
  · intro p k; exact mul_nonneg (by positivity) (pn_check (p:=p.val) h he ha hρ)
  · exact hρ
  · intro p
    let c:= prenex N.conduit l M e uJ θ ρ α p.val; let g k:= (ρ^k)⁻¹*c * ρ^(k:ℕ)
    have hv k:g k=c:=by unfold g; rw [mul_comm _ c,mul_assoc,inv_mul_cancel₀ _,mul_one]; positivity
    change ∑ k:Orders M,g k.val≤ (↑(M+2:ℕ):ℝ)*c
    simp only [hv,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
    exact le_rfl
  · intro p t U hh
    unfold issue prices; split
    next heT=> rw [heT]; exact excessFunds h he ht hr ha hz hρ hA hE U p.2.2 hh
    exact leafFunds h he ht hr ha hz hρ U p.2.2 hh _

  exact positions_pay h he hρ ha hd hp hη hq

lemma Prepared.ready {w:ℝ}(h : Prepared N l M e uJ θ ρ α a w η) (k : ℕ)(cut : ℝ):
    LeafReady χ k cut (issue H χ M) v j (fun i p=> prices N l M e uJ θ ρ α i.val p) (fun i=> carrier N.conduit l M e uJ θ ρ α i.val) ρ:=
  ⟨fun i t _=> fullShape M H χ i t,fun i p _ V=> h.holds i p V,h.scale,fun i p _ => h.pos i p,fun i _=> h.recognizes i,fun i _ V=> by rw [← Finset.sum_apply,fullIdentity]⟩

-- trim comment: Here proof addresses arbitrary prescription; no narrowed requirement on the actual leaf estimates.
end Mayer
end YM.RGLocalTaylor
