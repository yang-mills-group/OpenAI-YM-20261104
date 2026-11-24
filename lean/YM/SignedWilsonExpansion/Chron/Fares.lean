import YM.Integration.WilsonAddressedPhysicalCells
import YM.SignedWilsonExpansion.Purchase.China
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
/-!
# A single test registers ALL coordinates in a compact.Lambda.

Constructed before physical applications. This ensures point estimator available on even seams.Ceil positive mass.Interpolation elsewhere across collars.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.Integration.Cope
open MeasureTheory Lattice Wilson RG Filter Function Metric Extraction
open scoped Topology Classical BigOperators ContDiff
variable {n:ℕ}{σ r d:ℝ}{U Q:Set (Points n)}
open WilsonAddressedPhysicalCells
-- support closure & strict conf
lemma padded (p:IsCompact U)(q:U⊆conf n): ∃ ε> (0:ℝ),cthickening ε U⊆conf n:=by
    exact p.exists_cthickening_subset_open (conf_open _) q
lemma available (p:IsCompact U)(q:U⊆conf n):∃ (F:Test n) (ε:ℝ),0<ε∧ (∀ x,0≤(F x).re)∧ ∀ x∈ thickening ε U,0<(F x).re :=by
    obtain ⟨ε,hε,t⟩:= padded p q; obtain ⟨f,hp,hf,hB⟩:= IsOpen.exists_contDiff_support_eq (n:=(⊤:ENat)) (s:=thickening ε U) isOpen_thickening; let H(x):= Complex.ofReal (f x)
    have he:(tsupport H)= closure (thickening ε U):=by rw [←hp]; refine congrArg closure (Set.ext fun _=>?_); simp[H]
    have hQ: HasCompactSupport H:= IsCompact.of_isClosed_subset (show IsCompact (cthickening ε U) from p.cthickening) (isClosed_tsupport _) (show tsupport H⊆ _ from Set.Subset.trans ( le_of_eq he ) ( closure_minimal (thickening_subset_cthickening ε U) isClosed_cthickening))
    refine ⟨( ⟨ H, Complex.ofRealCLM.contDiff.comp hf,hQ,?_⟩: Test n ), ε,hε,fun x=> (hB ⟨x,rfl⟩).1,fun x hx=>?_⟩
    · rw [he]; exact fun x k=>t (closure_minimal (thickening_subset_cthickening ε U) isClosed_cthickening k)
    · exact lt_of_le_of_ne (hB ⟨x,rfl⟩).1 (Ne.symm (show f x≠0 from by rw [ ← hp ] at hx; exact hx)) -- support hp

variable (T: Test n) (ε:ℝ) (h:0<ε) (v:∀x,0≤(T x).re) (pv:∀ x∈ thickening ε U,0<(T x).re)
include h v pv
open private visible from YM.Integration.WilsonAddressedPhysicalCells
lemma actor (u:Fin n→ Cover)(hr:0<r)(hσ:0<σ)(K:Side)(p: (4*n:ℝ)*(σ/r)<ε) (hu:tag (σ/r) u∈ U) : mass T σ r K (wrap K ∘ u)≠0:=by
    let s:=σ/r; have hs:0<s:= div_pos hσ hr; let Q:=segment s u; let Y:=cell σ r K (wrap K∘u); have hY:MeasurableSet Y:= visible σ r K hσ _
    have hp:Q⊆Y:=by
        intro i hi; change atSite σ r K i= _; have h: address s i=u:=hi; unfold atSite; rw [← h]; apply congr_arg _; funext j k; unfold address; congr 1; change r* i j k/σ=i j k/s; unfold s; field_simp -- fix linter
    let T'(x:Points n):ℝ:= (T x).re; have hg:Integrable T:=T.continuous.integrable_of_hasCompactSupport T.hasCompactSupport
    have tg : (∫ x in Y,T' x)=RCLike.re (mass T σ r K (wrap K ∘ u)):= integral_re hg.integrableOn
    intro z; suffices G:0<∫x in Y,T' x by rw [tg,z,map_zero] at G; exact (lt_irrefl _) G
    apply ( integral_pos_iff_support_of_nonneg (f:=T') (μ:=volume.restrict Y) v (hg.re.integrableOn ) ).mpr; apply lt_of_lt_of_le _ (measure_mono (s:=Q) ?_); swap; · intro i hi; exact ne_of_gt (pv i ( mem_thickening_iff.mpr ⟨tag s u,hu,(lt_of_le_of_lt (show dist i (tag s u)≤_ from by rw [dist_comm,←(show address s i=u from hi)]; exact approximate hs i) p) ⟩))
    · rw [Measure.restrict_apply ( measurable_segment hs _ ),Set.inter_eq_left.mpr hp,cell_volume hs]; exact ENNReal.ofReal_pos.mpr (pow_pos hs _)
omit h v pv
lemma allowance (u:Fin n→ Cover)(j k:ℕ)(S:Schedule)(p:0<r) : (fun i=> S.gridPoint k (u i))= (fun i=> r • (tag (S.a k/r) u) i):=by
    funext i; apply PiLp.ext; intro a; change (S.a k * ( u i a:ℝ))=r*((S.a k/r)*(u i a:ℝ)); field_simp
open YM.SignedWilsonExpansion.Purchases.HalfRoof
lemma finite_mesh (h:IsCompact U)(p:0<σ): Set.Finite {x: Fin n→ Cover| tag σ x∈U}:=by
   obtain ⟨b,hb,hy⟩:= Salon.yield h; let K:= Nat.ceil (b/σ); let S:Set (Axis→ℤ):= Set.pi Set.univ (fun _=> Set.Icc ( - (K:ℤ)) (K:ℤ)); have ht:S.Finite:=Set.Finite.pi (fun _=>Set.finite_Icc _ _); refine (Set.Finite.pi (ι:=Fin n) (fun _=> ht)).subset (?_) -- may not univ placement type
   intro x hx i _ j _; apply abs_le.mp; have he : |σ*(x i j:ℝ)| ≤ b:=hy _ hx i j; rw [ abs_mul, abs_of_pos p ] at he; exact_mod_cast (show |(x i j : ℝ)| ≤ K from le_trans ((le_div_iff₀ p).mpr (by linarith only [ he ])) (Nat.le_ceil _) )
end YM.Integration.Cope
