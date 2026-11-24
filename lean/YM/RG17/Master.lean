import YM.RG17.Clocks
import YM.RG12.Canonical.FromFrames
import YM.RG12.Canonical.Low
import YM.OPE.Single

/-!
# Adapter at extraction: a CONCRETE full-column convention and grade prices

Work in the actual C.factory. For input/output points of the measuring
profiles, propose k columns in `RG12.Canonical` multiplied by the exact
threshold/g conversion and engineering. Prove the prices needed on the
*physical* quotient, including every row on a fixed coherent OPE system.

`entries` are those of the real construction. In particular this is NOT the
statement that they already coincide with an addressed or common-tag formal
one-mark proof calculus (letters in `C.label d` do not even have external test
derivative positions!). If comparing via those calculi need proof of conversion
to THIS convention/positions and bounds in it, or additional maps. Use these
as addresses only of actual primary fields after taking the physical quotient,
not as a proposed norm of an RG error prior to address summation. Scaling them
converts **cost units** and does not turn the leading germs into the required
Fk coefficients. `row_rate` will spend subpower costs on the spatial
error, not on any coupling remainder. In particular we are NOT assigning
the threshold-to-g step a polynomial-Λ bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17.Report
open Function Filter Set RG Source Lattice OPE PertExtension
open RG12
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {hC : C.Makes}

-- Exposed units to use on both correlations and projections.
abbrev thresholdFactor (C : Family G) (B : ℕ → ℝ) (m : ℕ) := (C.path.levels.budget m).threshold / coupling B m

def rescales (C : Family G) (B : ℕ → ℝ) (d m : ℕ) : Module.End ℂ (C.label d) :=
  (C.labels.level d).scaled (thresholdFactor C B m)

def master (C : Family G) (S : Table C.book) (M : ∀ d,ℕ → RepChart C d)
    (B : ℕ → ℝ) (d m : ℕ) : C.label d →ₗ[ℂ] S.Field d :=
  (engineering M d m).comp (rescales C B d m)

-- finite-cutoff master label (use `C.O` normalized convention). Importantly uses the
-- coupling on THAT cutoff, not the limit B read off the calendar. Yields `master`.
def finiteColumn (C : Family G) (hC : C.Makes) (d m N p : ℕ) (x : C.label d) : C.label d :=
  (((C.S.a m:ℝ)^d : ℝ):ℂ) • (atK C hC d m (N,p) (rescales C (fun j=> C.path.β N p j) d m x))

def limitColumn (C : Family G) (M : ∀ d,ℕ → RepChart C d) (B : ℕ → ℝ) (d m : ℕ) (x : C.label d) : C.label d :=
  (((C.S.a m:ℝ)^d : ℝ):ℂ) • (M d m (rescales C B d m x))

lemma project_limit (C : Family G) (S : Table C.book) (M : ∀ d,ℕ → RepChart C d) (B : ℕ → ℝ) (d m : ℕ) (x : C.label d) :
    S.project d (limitColumn C M B d m x) = master C S M B d m x := by
  rw [limitColumn,map_smul]; rfl

variable {M : ∀ d,ℕ → RepChart C d} {B : ℕ → ℝ}
variable {f : Extraction.Order} {cut : Filter UVIndex}

lemma tends_limit (hG:G.Simple) (hl : Running.isLimit C f B) (ho : Observing C hC cut M)
    (hf : cut ≤ f.fuse) (d m : ℕ) (x : C.label d) (hm : C.ref d ≤ m) :
    Tendsto (fun i : UVIndex=> finiteColumn C hC d m i.1 i.2 x) cut (𝓝 (limitColumn C M B d m x)) := by
  have ht := (observed_run hC hG hl m).mono_left hf
  have hp : Tendsto (fun i:UVIndex=> thresholdFactor C (fun j=> C.path.β i.1 i.2 j) m) cut (𝓝 (thresholdFactor C B m)) :=
    tendsto_const_nhds.div ht (coupling_pos hC hG hl m).ne'
  have hy : Continuous (fun t:ℝ=> (C.labels.level d).scaled t x) := by
    apply continuous_pi; intro i
    simp_rw [Labels.Frame.scaled_apply]; fun_prop
  have hv : Tendsto (fun i:UVIndex => rescales C (fun j=> C.path.β i.1 i.2 j) d m x) cut (𝓝 (rescales C B d m x)):=
    hy.continuousAt.tendsto.comp hp
  exact tendsto_const_nhds.smul (((continuous_fst.clm_apply continuous_snd : Continuous (fun p : RepChart C d × C.label d=> p.1 p.2)).continuousAt.tendsto).comp ((ho.tends d m hm).prodMk_nhds hv))

lemma scale_from_threshold (hG:G.Simple) (hC:C.Makes) (hl : Running.isLimit C f B) (d : ℕ) (x : C.label d) :
    RateLE atTop C.S.scale (fun m => mass C d (rescales C B d m x)) 0 := by
  let a : ℕ → ℝ := thresholdFactor C B
  have hx := C.S.divergent
  have ha : RateLE atTop C.S.scale a 0:=by
    have he : RateLE atTop C.S.scale (fun m=> (C.path.levels.budget m).threshold) 0 := RateLE.absBound 1 hx (Eventually.of_forall fun i=>
      by rw [Real.norm_of_nonneg (C.path.levels.budget i).threshold_pos.le]; exact (C.path.levels.budget i).threshold_le)
    have h : a = fun i=> (C.path.levels.budget i).threshold * (coupling B i)⁻¹:= by funext i; exact div_eq_mul_inv ..
    rw [h]; simpa using! he.mul ((coupling_rate hC hG hl).inv.pays hx)
  let F:= C.labels.level d
  change RateLE atTop C.S.scale (fun m=> ∑ i, ‖(rescales C B d m x) i‖) _
  apply RateLE.sum hx
  intro i _
  suffices h : RateLE atTop C.S.scale (fun m=> ‖a m^ (F.grades i).2‖ * ‖x i‖) 0 by
    apply h.congr (Eventually.of_forall ?_)
    intro m; simp only [rescales, Labels.Frame.scaled_apply,norm_mul,Complex.norm_real]; rfl
  simpa using! (((ha.pow (F.grades i).2 hx).norm).mul (RateLE.const ‖x i‖ hx))

variable (F : Spec.Final C f S) (P : OPE.Prescription F.sector.derivatives) (hP : P.Coherent)
variable [cut.NeBot]

lemma entry0_master (hG:G.Simple) (ho : Observing C hC cut M)
    (B) (k : ℕ) (he : C.ref 0 ≤ k) (x : C.label 0):
    master C S M B 0 k x = x 0 • S.unit 0 := by
  obtain ⟨z,rfl⟩:= unit_spans hG C 0 k (by omega) x
  have hx := ho.unit _ k he
  let L := C.labels.level 0
  rw [map_smul]
  have heq: unitVec L C.path k= L.e0:= by simp [unitVec]
  change z • master C S M B 0 k (unitVec L C.path k)= (z • unitVec L C.path k) 0 • S.unit 0
  rw [heq]
  change z • (engineering M 0 k (L.scaled _ L.e0)) = _
  rw [L.scaled_unit, engineering_at,← heq,hx]
  change z • (_ • (S.unit 0))=(z • unitVec L C.path k) 0 • S.unit 0
  rw [heq]; simp [Labels.Frame.e0]

-- true grade cost on S for the actual k-column
include F P hP
theorem row_rate (hs : Services C f S) (ho : Observing C hC cut M) (hu : cut ≤ f.fuse)
    (hB : Running.isLimit C f B) (d : ℕ) (x : C.label d) (w : Mode F.sector.derivatives) (hw : w.fst ≤ d) :
    RateLE atTop C.S.scale (fun m=> P.test w d (master C S M B d m x)) (-(w.fst:ℝ)) := by
  have hg := hs.simpleGate
  obtain ⟨W,b,D,hL⟩:=hs.purchase
  obtain ⟨A,L,z,V,hV⟩:=hs.along
  let C₀:= C.path.levels
  let X m:= rescales C B d m x
  let Y:= (P.test w d).comp (S.project d) |>.toContinuousLinearMap
  have he(m : ℕ) : P.test w d (master C S M B d m x)= (((C.S.a m)^d:ℝ):ℂ) • Y (M d m (X m)):= by
    unfold master; rw [LinearMap.comp_apply, engineering_at,map_smul]; rfl
  have hT:= C.S.divergent
  have hm : RateLE atTop C.S.scale (fun m=> mass C d (X m)) 0:= scale_from_threshold hg hC hB d x
  have ha:= (spacing_rate C).power d
  let a m := C.S.a m ^ d
  -- q.e.d. with projection e−1 killed before bounding test, including the
  -- weaker `d` price when e=0.
  have hk : Tendsto (fun m=> C.S.scale m / C.S.scale m) atTop (𝓝 1):=
    tendsto_const_nhds.congr' ((hT.eventually_gt_atTop 0).mono fun _ hi=> (div_self (ne_of_gt hi)).symm)
  rcases Nat.eq_zero_or_pos w.fst with hz | hz
  · rw [hz,Nat.cast_zero,neg_zero]
    let u m:= Columns.juice C.path.levels m * (C.S.a (C.ref d)/C.S.a m)^d
    have hf : RateIs atTop C.S.scale u (d:ℝ):=by
      simpa only [mul_neg,mul_one,sub_neg_eq_add,zero_add] using!
        (Columns.juice_rate_seq C tendsto_id hk).mul (((RateIs.const hT (C.S.a_pos _)).div (spacing_rate C)).power d)
    let t m:= a m * (‖Y‖ * (u m * mass C d (X m)))
    have ht : RateLE atTop C.S.scale t 0:= by
      simpa using! (ha.pays hT).mul ((RateLE.const ‖Y‖ hT).mul ((hf.pays hT).mul hm))
    refine ht.of_norm_le ?_
    filter_upwards [eventually_ge_atTop (C.ref d)] with m Hm
    obtain ⟨q,hq,hQ⟩:= ho.purchase d m Hm le_rfl (X m)
    have H : ‖M d m (X m)‖ ≤ u m * mass C d (X m) := by
      apply le_of_tendsto hq.norm; filter_upwards [hQ,ho.grows.eventually_ge_atTop m] with i hi hk
      have Hu:0 ≤ u m:= mul_nonneg (zero_le_one.trans (Columns.juice_pos ..)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)
      exact (Columns.whole_origin hV _ Hm hk).trans (mul_le_mul_of_nonneg_left hi Hu)
    rw [he m, norm_smul,Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (C.S.a_pos _).le _)]
    exact mul_le_mul_of_nonneg_left ((Y.le_opNorm _).trans (mul_le_mul_of_nonneg_left H (norm_nonneg _))) (pow_nonneg (C.S.a_pos _).le _)
  let c:=w.fst-1
  have hc : c<w.fst:=by unfold c; omega
  let u m:= Columns.fare C m d c
  have hf: RateIs atTop C.S.scale u ((d-w.fst:ℕ):ℝ):= by
    have hf:= Columns.fare_rate (e:=c) (d:=d) hL.toTableTickets tendsto_id hT hk
    have h : c+1=w.fst:=by unfold c; omega
    rw [h, mul_one] at hf; exact hf
  let t m:= a m * (‖Y‖ * (u m * mass C d (X m)))
  have ht : RateLE atTop C.S.scale t (-(w.fst:ℝ)):= by
    convert! (ha.pays hT).mul ((RateLE.const ‖Y‖ hT).mul ((hf.pays hT).mul hm)) using 1
    norm_num [Nat.cast_sub hw]; ring
  refine ht.of_norm_le ?_
  filter_upwards [eventually_ge_atTop (C.ref d)] with m Hm
  obtain ⟨q,hq,hQ⟩:= ho.purchase d m Hm le_rfl (X m)
  obtain ⟨y,⟨p,hp⟩,hy⟩:= Columns.limit_cap hL.toTableTickets hg hV F.phase.transport.injection (lt_of_lt_of_le hc hw) q _ hu Hm hQ hq
  have hY : Y y=0:=by
    change P.test w _ (S.project _ y)=_
    rw [← hp,Prescription.affinity F.room.kernel.laws.toSymmetric F.phase.transport.injection, Prescription.highVan F.room.kernel.laws.toSymmetric F.phase.transport.injection hP w hc]
  rw [he m,norm_smul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos _).le _), show Y (M d m (X m))=Y (M d m (X m) - y) by rw [map_sub,hY,sub_zero]]
  exact mul_le_mul_of_nonneg_left ((Y.le_opNorm _).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))) (pow_nonneg (C.S.a_pos _).le _)
end YM.RG17.Report
