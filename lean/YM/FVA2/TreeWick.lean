import YM.FVA2.TreePlane
import YM.MS.Swirl.Plane

/-!
# Rooted top LPT in an arbitrary tree vs in an arbitrary based linear gauge.

One step of this proof is **projection** of the full rooted exponent; it is
only after completing that argument that one can discard ghost vertices in the
tree rule. -/

noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inversion
open Matrix Finset Function Set Filter Lattice MS MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open MS.Native MS.Bare MS.Book MS.Book.Convolve MS.Puff MS.Puff.Actors MS.Puff.Mom
open MS.Cylinder MS.Cylinder.Taylor MS.Koszul Ends ArrayMap Lag Substitute Letter
open Inserted PertExtension PertExtension.Orb
open scoped Topology ContDiff Classical
variable {n:Side} {G:Gauge}
open Choice

def fullRoot (G:Gauge) (n:Side) := (root n).total (priorRoot G n)

local notation "Φ"=> allLetters G n
local notation "Θ"=> fullRoot G n

/-- Extract the whole quadratic coefficient, not only its AA block. -/
def rootedVertex (G:Gauge)(n:Side) : SpecB (allLetters G n):= fun k=> if k=0 then 0 else fullRoot G n k
local notation "U" => rootedVertex G n
private lemma augment : useN.refineV (Θ 0) + U=Θ := by
  funext i; rw [Pi.add_apply]
  unfold rootedVertex; split_ifs with h
  · subst i; rw [add_zero]; exact if_pos rfl
  unfold SplitP.refineV; rw [if_neg (show i≠useN.origin from h),zero_add]
lemma root_regular : Γ U p := by
  obtain hv:= (root n).total_limits (prior_root_prop G n)
  rw [show U=Θ-useN.refineV (Θ 0) from eq_sub_of_add_eq (by rw [add_comm]; exact augment)]
  exact (allIndex (FeeP p) _).sub_mem hv (refineπ _ _ (hv _ (Set.mem_univ _)))
lemma parity_issue : EvenSeries p U := by
  apply even_coeff _|>.mpr; intro i; unfold rootedVertex; split
  exact Koszul.Pure.zero
  exact (even_coeff _).mp ((root n).total_even (S:=priorRoot G n)) i

namespace Choice
variable (T:Choice G n)

abbrev bosEven : Sector T.CO := fun _=>false
def boson (k:ℕ) : BL T.CO := if k=0 then 0 else (rankLevel 2 (T.coInk (priorRoot G n))+rankLevel 0 (T.coInk measure_term)) k
abbrev relative := exp0 T.bosEven T.boson
def comark (F : RootX G n→ℝ) (rank : ℤ) := rankLevel rank (T.coInk F)
lemma boson_regular : Γ T.boson T.bosEven := by
  intro i _; unfold boson; split; exact (FeeP _).zero_mem
  have hk (F:RootX G n→ℝ)(hf:germ F) : Symm T.bosEven (T.coInk F) := ink_s _ (fun _ he=>Bool.noConfusion he) hf
  apply (FeeP _).add_mem
  · refine ⟨ ?_, minH (Limit.mod _ _)⟩; apply symRank _ (hk (priorRoot G n) (prior_root_prop ..).smooth)
  refine ⟨ ?_, minH (Limit.mod _ _)⟩; exact symRank _ (hk _ measure_germ)
where
  symRank {u : Raw T.CO ℂ} (i:ℤ)(h : Symm T.bosEven u) : Symm T.bosEven (mask i u) := by
    intro l a b x; by_cases he: ((l++a::b::x).length:ℤ)=i
    · rw [enough _ he,enough _ (by simpa using he),h]
    rw [strange _ he,strange _ (by simpa using he), mul_zero]
lemma comark_regular (r:ℤ)(F: RootX G n→ℝ) (hf:germ F): Γ (T.comark F r) T.bosEven :=
  fun i _=> ⟨boson_regular.symRank T (i+r) (ink_s _ (fun _ he=>Bool.noConfusion he) hf), minH (Limit.mod _ _)⟩

local notation "Kp"=> ξ[intoC T.projectChart]
local notation "Kt"=> ξ[intoC T.appear]

lemma erase_ghost : promote Kp U=promote Kt T.boson := by
  funext r; simp only [promised]; unfold rootedVertex boson; split_ifs with he; · rw [map_zero,map_zero]
  unfold fullRoot Ends.total; simp only [Pi.add_apply,rankLevel,map_add,in_rank]
  have hh:= T.cost_after r (by omega); unfold rankLevel at hh; rw [hh, show
      ink tangentVec ((target G n) ∘ T.cut)=Kt (T.coInk (priorRoot G n)) from
        (cut_ink T _ (prior_root_prop ..).smooth).symm.trans (co_cut T _ (prior_root_prop ..).smooth),
    show Kp (HaarBody _ _ _)=_ from co_cut T measure_term measure_germ ]; -- inspect
lemma all_monomial (E:RootX G n→ℝ)(h:germ E)(d:ℤ) : promote Kp (rankLevel d (ink tangentVec E))=
    promote Kt (comark T E d) := by funext i; simp_rw [promised,comark,rankLevel,in_rank,T.co_cut E h]

abbrev C_field := intoC T.Ctilt
abbrev leftM := intoC T.fix
local notation "Wp"=> grain T.C_field T.leftM

lemma ward_inputs (h:Even n.val) :
    let S:= intoC (hesT G n); let GA:=intoC (gaugeMatrix G n)
    Sᵀ=S ∧ S * GA=0 ∧ T.C_fieldᵀ=T.C_field ∧ T.leftM*GA=1 ∧ T.C_field*S=1-GA*T.leftM := by
  have ht:= Ends.cost_kernel _ (prior_root_prop G n)
  have hx:= Ends.cost_symmetric _ (prior_root_prop G n)
  refine ⟨congr_arg intoC hx,?_,congr_arg intoC T.c_symm,?_,?_⟩
  · rw [←into_mul,show hesT G n*gaugeMatrix G n=_ from ht,into_zero]
  · unfold leftM; rw [←into_mul,T.fixes,into_one]
  unfold C_field leftM; rw [← into_mul,T.actual_covariance h,into_sub,into_mul,into_one]

/-- Reduction to ordinary insertion-bearing Wick diagrams on the chosen tree. -/
lemma restrict_integral (V : SpecB Φ) (h : Γ V p) (W : SpecB T.CO)
    (hv : Γ W T.bosEven)(hp : promote Kp V=promote Kt W):
    ℶV Wp ((PermV p).core (exp0 p U) V) =
      ℶV T.lineCo ((PermV T.bosEven).core T.relative W) := by
  let Y:= (PermV p).core (exp0 p U) V
  let X:= (PermV T.bosEven).core T.relative W
  have hz : promote Kp Y= promote Kt X := by
    have ht : ∀ f g, promote Kp ((PermV p).core f g)= (PermV p).core (promote Kp f) (promote Kp g):=
       fun f g=> ((tether _ T.paysT).Extrapolation useN).craft f g
    have hu : ∀ f g, promote Kt ((PermV T.bosEven).core f g)= (PermV p).core (promote Kt f) (promote Kt g) :=
       fun f g=> ((tether _ T.tether_A).Extrapolation useN).craft f g
    unfold Y X; rw [ht,hu,hp,exp_change _ T.paysT,erase_ghost,relative,exp_change _ T.tether_A]
  funext i; change View Wp (Y i)=View T.lineCo (X i)
  have hh : Γ Y p:= ΤΓ_pair (expΓ root_regular) h
  have hi : Γ X T.bosEven:= ΤΓ_pair (expΓ T.boson_regular) hv
  rw [show View Wp (Y i)= _ from (T.view_P (fee_spec (hh i (Set.mem_univ _))).2).symm]
  rw [ show Kp (Y i)= Kt (X i) from congr_fun hz i]
  exact T.slice_view _ (fee_spec (hi i (Set.mem_univ _))).2

lemma restrict_vacuum : ℶV Wp (exp0 p U)=ℶV T.lineCo T.relative := by
  let F := PermV (p (X:= Z G (OEdge n)) (Y:=Z G (Vert n))) -- p expects? named
  let E := PermV T.bosEven
  convert! T.restrict_integral F.unit _ E.unit _ _ using 2
  · exact (F.identityR _).symm
  · exact (E.identityR _).symm
  · exact refineπ _ _ feeUnit
  · exact refineπ _ _ feeUnit
  exact ((tether _ T.paysT).Extrapolation useN).unit.trans
    ((tether _ T.tether_A).Extrapolation useN).unit.symm

/-- Tree and based-landau projection supplier, retaining vacuum and all marks. -/
theorem compares_root (h:Even n.val) (V : SpecB Φ)
    (he : MarkOK (Letter.bond (Z G (OEdge n)) (Z G (Vert n))) Θ V)
    (W : SpecB T.CO) (hv : Γ W T.bosEven) (hp : promote Kp V=promote Kt W)
    (C:Matrix (Z G (OEdge n)) (Z G (OEdge n)) ℂ)(L:Matrix (Z G (Vert n)) (Z G (OEdge n)) ℂ)
    (hc:Cᵀ=C)(hL:L*intoC (gaugeMatrix G n)=1)(hC:C*intoC (hesT G n)=1-intoC (gaugeMatrix G n)*L)
    (z : ℕ→ℂ): Endμ (grain C L) p U V z ↔ Endμ T.lineCo T.bosEven T.boson W z := by
  obtain ⟨ha,hG,hx,h₁,h₂⟩:= T.ward_inputs h
  have hq:= total_hessian _ (prior_root_prop G n)
  let B:= Letter.bond (Z G (OEdge n)) (Z G (Vert n))
  have hh (V : SpecB Φ)(hy : MarkOK B Θ V) : ℶV (grain C L) ((PermV p).core (exp0 p U) V)=
      ℶV Wp ((PermV p).core (exp0 p U) V) :=
     closed_wick_eq hq root_regular parity_issue (if_pos rfl) (by
       change tokM B (useN.refineV (Θ 0)+ U)=_; rw [augment]; exact (root n).master_eq (prior_root_prop ..))
        (by change MarkOK B (useN.refineV (Θ 0) + U) V; rw [augment]; exact hy) ha hG hc hL hC hx h₁ h₂
  unfold Endμ
  rw [hh V he,T.restrict_integral V he.finiteF W hv hp];
  have ht:= hh (PermV p).unit (MarkOK.unit (total_even _ )); rw [(PermV p).identityR] at ht
  rw [ht,T.restrict_vacuum]
end Choice
end YM.FVA2.Inversion
