import YM.Frontier6.Trajectory.Exports
import YM.Frontier6.Pair.Reannounce
import YM.Frontier6.Pair.Contexts

/-! Take continuum limits with the whole pair and every priced projection.
Keep one match valid for any exterior **with current off-seam tiling**. q costs
from exact primary continuation: this isn't an all-orders claim! -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Canvas
open Function Filter Set Lattice Wilson RG Source Labels MergeProof MergeProof.Ribbons Next.UVStress
open Bid Spec Extraction.Lease Cells Extraction.Around OS Word MeasureTheory
open Platform Next.Extract Dash PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order} {f:Filter (ℕ×ℕ)}
variable {j k m b n D d t : ℕ}
variable {S T:Table C.book}{M:ℕ→Table C.book}{R:Bin T}{Y:DiffPlan S}
variable (H:Base C F T M R S Y) (K:Spec.Final C F S)(h:PairProducer C)(hG:G.Simple)(hW: Extraction.Wcmain C)

structure ReferenceFit (K:Spec.Final C F S) (q:C.label D)(m:ℕ)(A:ℝ) : Prop where
    whole : ‖q‖ ≤ voyage C D m D*A
    below (e:ℕ)(he:e<D): ∃ v:C.label D,S.project _ v∈LinearMap.range (K.sector.derivatives.rise he.le)∧ ‖q-v‖ ≤ voyage C D m (D-(e+1))*A

include H K h hG
lemma sublimit_grade (q:Rowe C D)(Q:C.label D)[f.NeBot](ht:f ≤ F.fuse)(hQ:Tendsto q f (𝓝 Q)) (A:ℝ)(hm:C.ref D≤ m)
    (hq: ∀ᶠ i:ℕ×ℕ in F.fuse, m ≤ i.1 ∧ quota C D m i.1 i.2 (q i) ≤ A) : ReferenceFit K Q m A:=by
   obtain ⟨W,r,P,h₀,h₁,h₂⟩:= h.launches; let hM:= H.family
   have hp:∀ᶠ i:ℕ×ℕ in F.fuse, ‖q i‖≤ voyage C D m D*A := hq.mono fun i hi=> (from_whole C (p:=i.2) hM hi.1 hm (q i)).trans (mul_le_mul_of_nonneg_left hi.2 ((voyage_pitch C D D).pos m|>.le)) -- i.2 may need explicit
   refine ⟨le_of_tendsto hQ.norm (Eventually.filter_mono ht hp),fun e he=>?_⟩
   let Z:= voyage C D m (D-(e+1))*A
   let fact i (z:C.label D):Prop:= shed (C.labels.level D) e ((C.factory D i.1 i.2).terminal.symm z)=0∧ ‖q i-z‖ ≤ Z
   have hx:∀ᶠ i in F.fuse, ∃ z:C.label D, fact i z:=by
       filter_upwards [hq] with i hi
       obtain ⟨w,hz,hW⟩:= from_front C (p:=i.2) hM h₁ h₀.costs.cost h₀.costs.back e he hi.1 hm (q i)
       refine ⟨w,hz,hW.trans ?_⟩; exact mul_le_mul_of_nonneg_left hi.2 ((voyage_pitch C D _).pos m|>.le)
   let w : Rowe C D:=fun i=> if h:∃ z,fact i z then h.choose else 0
   have hx: ∀ᶠ i in F.fuse, fact i (w i):= hx.mono fun i hi=> by unfold w;rw [dif_pos hi];exact hi.choose_spec
   let Z':= Z+ voyage C D m D*A; have hw:∀ᶠ i in F.fuse, ‖w i‖ ≤ Z':= (hp.and hx).mono fun i hi=>by
       have hv:= hi.2.2; exact (show ‖w i‖≤ ‖q i-w i‖+‖q i‖ by rw [norm_sub_rev]; simpa using norm_sub_le (w i - q i) (-(q i))).trans (add_le_add hv hi.1)
   obtain ⟨ℓ,hℓ,H',x,hx'⟩:=finite_extract w Z' (Eventually.filter_mono ht hw)
   refine ⟨x, legacy_sublimit hM hG h.stops h₁ h₀ h.stores H K.phase.transport.injection he w ⟨_,hw⟩ (hx.mono (fun _ h=> h.1)) (le_trans hℓ ht) hx',le_of_tendsto (((hQ.mono_left hℓ).sub hx').norm) (Eventually.filter_mono (le_trans hℓ ht) (hx.mono fun _ hi=> hi.2))⟩

include hW
variable (B:C.label d) (U:C.label t)
structure Priced (f : Extraction.Order) (b j:ℕ)(x:Lattice.Cover)(B:C.label d)(U:C.label t)(z:C.label D)(ε:ℝ):Prop where
    retires : ∃ ℱ:Filter (ℕ×ℕ),ℱ ≤ f.fuse ∧ ℱ.NeBot∧ RealPair B U z b j x ε ℱ

lemma cashier {p q ε ε':ℝ} (x:Lattice.Cover)(hY:C.ref D≤ b)(hm:b ≤ m)(hx:fuga C.path.levels (m+1)/16 ≤ ‖C.S.gridPoint j x‖)(hz:‖C.S.gridPoint j x‖ ≤ 4*fuga C.path.levels m)(hp:ShellPairs C b j m d t D B U F q ε)(he:ε<ε') :∃ z:C.label D, Priced F b j x B U z ε' ∧ ReferenceFit K z m q:=by
   obtain ⟨w,hw⟩:=hp.corners x hx hz
   have hv: ∀ᶠ i:ℕ×ℕ in F.fuse,m ≤ i.1 ∧ quota C D m i.1 i.2 (w i) ≤ q:= hw.mono fun i hi=> ⟨hi.choose_spec.1,hi.choose_spec.2.1⟩
   have hg:∀ᶠ i:ℕ×ℕ in F.fuse, ‖w i‖≤ voyage C D m D*q:= hv.mono fun i hi=> (from_whole C (p:=i.2) H.family hi.1 (le_trans hY hm) (w i)).trans (mul_le_mul_of_nonneg_left hi.2 ((voyage_pitch C D D).pos m|>.le))
   obtain ⟨ℓ,hl,hL,z,hZ⟩:= finite_extract w _ hg
   refine ⟨z,⟨ℓ,hl,hL,realize_limit B U z hl w hZ x ε ε' he H.family hW hY ?_⟩,sublimit_grade H K h hG w z hl hZ q (hY.trans hm) hv⟩
   exact Eventually.filter_mono hl (hw.mono fun i hi=>⟨hi.choose,hi.choose_spec.2.2⟩)

-- Insert trajectory's estimates, choosing k once after requests. q exponent chosen M-D by caller. Provide conversion to all seasons `O(a_m^-cost)`.
omit H K hG hW
end YM.Frontier6.Canvas
