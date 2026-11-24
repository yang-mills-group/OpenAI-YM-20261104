import YM.Comparison.RG02.Moving.Gate
import YM.Comparison.RG02.Moving.Leads
/-!
# Use moving gaussian on same branch, fold to Fk and pass projected derivative log.

Partition/cumulant identities use these turns in the combined grading.
No post-block resets folded into the coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving.Shift
open Function Filter Finset MeasureTheory YM.Marker YM.Multi Order Assembly Cumulants
open PertExtension.Series PertExtension.Series.Tested Laplace Path
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open YM.Precision YM.Next.SectorChange Gaussian Affinity
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} (r : ℕ)
variable {I X : Type} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
local notation "δ" => Grade R r
local notation "M" => Board R r

/-- Results match the same period, up to optional affine budget presentation equivalent below. -/
structure TrueAt (R : Census V) (r : ℕ) (u:ℝ→Grade R r) (A : Grade R r) : Prop where
   unfoldLaw : Seen u
   ready : ∀ᶠ t in 𝓝 0,Order.Symmetric (u t)
   port : fuse R r u=A
-- map report directions
structure Ready (u : ℝ→Grade R r) (A : Grade R r) : Prop extends TrueAt R r u A where
   leading : ∀ᶠ t in 𝓝 0,UnitLeading (u t)
local notation "A"=> Assembly.prescription
namespace Cargo
open YM.Comparison.RG02.Moving.Cargo
variable (x:X) (l:Hot R→ℕ) (F:Hot R→House X I→ℂ) (f:House X I→ℝ)
    (C:Field X I)

local notation "T"=> cost x l F f r C
lemma watches (p : YM.Next.Rank.Normal.poly I) : ContDiffAt ℝ ω (fun t=> (Cloud.wick (C.Q (path x t)) (C.symmetric (path x t)) 0) p) 0 := by
   let L (t:Regulator X) := (Cloud.wick (C.Q t) (C.symmetric t) 0) p
   have he : ContDiffAt ℝ ω L 0:= C.wick_stays _
   exact (Eq.mp (by rw [path0 x]:ContDiffAt ℝ ω L 0=ContDiffAt ℝ ω L (path x 0)) he).comp 0 (smooth_path x).contDiffAt
omit [Fintype V] in
lemma cloud_seen (L : Hot R → YM.Next.Rank.Normal.poly I) : Seen (fun t=> Cloud.prescription (C.Q (path x t)) (C.symmetric (path x t)) 0 L) := by
  constructor; intro i; unfold Cloud.prescription Poly.inject; exact watches x C (Cloud.integrand L i)
lemma seen : Seen T := by unfold cost Assembly.prescription; exact cloud_seen x C _
lemma symmetric : ∀ᶠ t in 𝓝 0,Order.Symmetric (T t) := (path_home x).eventually C.positive |>.mono (fun _ hi=> prescription_sym _ _ _ _ _ _ _ hi)
local notation "W"=> cost x l F (C.retax f) r C

variable (hf : Ray (C.Q 0) f) (hF : ∀ i,GradeAt (l i) (F i))
include hf hF
lemma phate : Ready r W (Assembly.prescription (1,x,0) (reach X) l F f (C.Q 0) (C.symmetric 0) r) := by
   refine ⟨⟨seen .., symmetric ..,?_⟩, Eventually.of_forall fun _=> Assembly.prescription_unit ..⟩
   refine (sym_coeff _ _ (fuse_symmetric (symmetric ..)) (Assembly.prescription_sym _ _ _ _ _ _ _ C.flat)).2 fun i hi=> ?_
   ext s; exact (valued (seen r x l F (C.retax f) C) (symmetric ..) hi).symm.trans (YM.Comparison.RG02.Moving.Cargo.leads x r s C hf hF _ hi).symm
end Cargo

variable {r} {u:ℝ→Grade R r} {P : Grade R r}
lemma Ready.turnRatio (h:Ready r u P): Ready r (Order.ratio ∘ u) (Order.ratio P) :=
   ⟨⟨(fuse_ratio h.unfoldLaw h.leading).1,(h.leading.and h.ready).mono (fun _ hx=> sym_ratio hx.1 hx.2), (fuse_ratio h.unfoldLaw h.leading).2.trans (congrArg Order.ratio h.port)⟩,h.leading.mono (fun _ h=> Order.ratio_quiet h)⟩
lemma Ready.vacant (h:Ready r u P) : Ready r (denominator ∘ u) (denominator P) :=
   ⟨⟨h.unfoldLaw.across,h.ready.mono (fun _ ht=> ht.vacant), (absorb u).symm.trans (congrArg denominator h.port)⟩, leads_vac h.leading⟩
lemma Ready.over (h:Ready r u P) : TrueAt R r (connected ∘ u) (connected P):=
   ⟨(fuse_log h.unfoldLaw h.leading).1,(h.leading.and h.ready).mono (fun _ he=> he.2.log he.1), (fuse_log h.unfoldLaw h.leading).2.trans (congrArg connected h.port)⟩
lemma TrueAt.measures (h: TrueAt R r u P) (s:R.Mode) (k:ℕ) (hk:k≤r) : motion (fun t:ℝ=> (value (t:ℂ) (u t)).part s) k = detail P s k := h.port ▸ (valued h.unfoldLaw h.ready hk)
lemma Ready.projects (h:Ready r u P) (s:R.Mode) (k:ℕ) (hk:k≤r) :
   motion (fun t:ℝ=> (value (t:ℂ) (Order.logVac (u t))).part s) k= detail (Order.logVac P) s k ∧
     motion (fun t:ℝ=> (value (t:ℂ) (Order.logMarked (u t))).part s) k= detail (Order.logMarked P) s k := ⟨h.vacant.over.measures s k hk,h.turnRatio.over.measures s k hk⟩
lemma TrueAt.concentrate (h: TrueAt R r u P) (s:R.Mode) (k:ℕ) (hk:k≤r) : detail P s k=∑ i∈range (k+1), motion (fun t=>detail (u t) s (k-i)) i := by rw [← h.port,bore h.unfoldLaw h.ready hk]
end YM.Comparison.RG02.Moving.Shift
