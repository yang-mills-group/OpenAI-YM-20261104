import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeEdgeRows
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeEdgePowers

/-! Sharp replacement on the actual selected reader and on the exact
flat finite fusion tree of the public statement. The terminal Haar and
reality mean is evaluated once, after all nonroot factors are public. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeEdgeTelescope
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Nesting OPE.Nesting.Atom OPE.Log MeasureTheory
open YangMills YangMills.Hierarchy
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross WilsonCenteredNestedProducts
open WilsonCenteredNestedPairHaar WilsonSharpPhysicalTreeEdgeRows WilsonSharpPhysicalTreeEdgePowers
open scoped Classical Topology BigOperators
attribute [local instance] measO borelO YM.Work.A15.compact_ortho

variable {g : GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (t : FusionTree)
local notation "T" => hierarchy F Q

def cap (m : ℕ) (D : Fin t.branches → ℕ) : t.Vertex → ℕ := Fin.cases m D

lemma retained {D : Fin t.branches → ℕ} (u : t.Selection T D) (m : ℕ) (c : Q.channels m)
    (v : t.Vertex) : (t.vertexChannel T u m c v).1 ≤ cap t m D v := by
  refine Fin.cases le_rfl (fun i => Nat.le_of_lt_succ (u i).1.isLt) v

def rawAt (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    {D : Fin t.branches → ℕ} (u : t.Selection T D) (m : ℕ) (c : Q.channels m)
    (v : t.Vertex) (k : Ortho) (b : Bool) : ℂ :=
  let h := t.vertexChannel T u m c v
  raw F Q (cap t m D v) h.1 h.2 (t.positions (v := v) x z) (t.childField T a u (v := v)) (z v) k b

def publicAt (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    {D : Fin t.branches → ℕ} (u : t.Selection T D) (m : ℕ) (c : Q.channels m)
    (v : t.Vertex) : ℂ :=
  let h := t.vertexChannel T u m c v
  express Q h.1 h.2 (t.positions (v := v) x z) (t.childField T a u (v := v)) (z v)

def contracted (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (D : Fin t.branches → ℕ) (m : ℕ) (c : Q.channels m) (k : Ortho) (b : Bool) : ℂ :=
  ∑ u : t.Selection T D, ∏ v : t.Vertex, rawAt F Q t a x z u m c v k b

def held (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (D : Fin t.branches → ℕ) (m : ℕ) (c : Q.channels m) (k : Ortho) (b : Bool) : ℂ :=
  ∑ u : t.Selection T D, (∏ i : Fin t.branches, publicAt F Q t a x z u m c i.succ) *
    rawAt F Q t a x z u m c 0 k b

theorem measurable_contracted (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4)
    (z : t.Vertex → E4) (D : Fin t.branches → ℕ) (m : ℕ) (c : Q.channels m)
    (opened : ∀ v, orbitMargin Q.port (cap t m D v) (t.positions (v := v) x z) (z v)) (b : Bool) :
    AEStronglyMeasurable (fun k => contracted F Q t a x z D m c k b) haar := by
  unfold contracted
  exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun u _ =>
    Finset.aestronglyMeasurable_fun_prod Finset.univ fun v _ =>
      (integrable_raw F Q (cap t m D v) (t.vertexChannel T u m c v).1
        (t.vertexChannel T u m c v).2 (t.positions (v := v) x z)
        (t.childField T a u (v := v)) (z v) (opened v) b).aestronglyMeasurable

theorem root (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (D : Fin t.branches → ℕ) (m : ℕ) (c : Q.channels m)
    (live : orbitMargin Q.port m (t.positions (v := 0) x z) (z 0)) :
    mean (held F Q t a x z D m c) = t.iterated T a x z D m c := by
  rw [show mean (held F Q t a x z D m c) =
      ∑ u : t.Selection T D, (∏ i : Fin t.branches, publicAt F Q t a x z u m c i.succ) *
        publicAt F Q t a x z u m c 0 from
      root_mean F Q m c (t.positions (v := 0) x z) (fun u => t.childField T a u (v := 0))
        (z 0) live (fun u => ∏ i : Fin t.branches, publicAt F Q t a x z u m c i.succ)]
  apply Finset.sum_congr rfl
  intro u _
  change _ = ∏ v : t.Vertex, publicAt F Q t a x z u m c v
  rw [Fin.prod_univ_succ, mul_comm]

private lemma small_scales {P : ℝ → Prop} (p : ∀ᶠ r : ℝ in 𝓝[>] 0, P r) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ a, 0 < a → a ≤ r → P a := by
  obtain ⟨e,ep,inside⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp p
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ge_mem_nhds ep)] with r re a ap ar
  exact inside ⟨ap,ar.trans re⟩

/-- One constant, log exponent, and small-root threshold for the complete
physical roster of a fixed tree and cutoffs. Every admissible array is
quantified afterwards, including independent arbitrarily small ratios. -/
theorem original (fac : Facilities C f S) (foundation : Foundation F Q)
    {l : Filter (ℕ × ℕ)} [l.NeBot] (lo : l ≤ f.fuse)
    (ticket : MatrixTicket (C := C) S F.sector.derivatives l)
    (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ) (c : Q.channels m)
    {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃ (j : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (β : ℝ), β ≤ 1 →
      ∀ s x z, t.Admissible r β M η s x z →
      (∀ k b, ‖contracted F Q t a x z D m c k b - held F Q t a x z D m c k b‖ ≤
        A * attachedBase T t a s m * (∏ v, shell (s v)^j) * t.cutoffGain D s) ∧
      ‖mean (contracted F Q t a x z D m c) - t.iterated T a x z D m c‖ ≤
        A * attachedBase T t a s m * (∏ v, shell (s v)^j) * t.cutoffGain D s := by
  let U := t.Selection T D
  let I := U × t.Vertex
  let offer (i : I) (j : ℕ) (B : ℝ) := ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ (p : t.Child i.2 → E4) (o : E4), WithinRoom r M η p o → ∀ k b,
    let h := t.vertexChannel T i.1 m c i.2
    let labels := t.childField T a i.1 (v := i.2)
    Priced (raw F Q (cap t m D i.2) h.1 h.2 p labels o k b) (express Q h.1 h.2 p labels o)
      (wage j B r * rowPrice labels h.1 r) (r ^ (cap t m D i.2+1-h.1))
  have source (i : I) : ∃ j B, 0 ≤ B ∧ offer i j B := by
    exact WilsonSharpPhysicalTreeEdgeRows.original F Q fac foundation lo ticket
      (t.childField T a i.1 (v := i.2)) (cap t m D i.2) _ (retained F Q t i.1 m c i.2) _ Mn ηp
  have up (i : I) (k : ℕ) (B : ℝ) (j : ℕ) (V : ℝ) (kj : k ≤ j) (Bn : 0 ≤ B)
      (BV : B ≤ V) (old : offer i k B) : offer i j V := by
    filter_upwards [old,(show ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r from self_mem_nhdsWithin)]
      with r paid rp p o fit K b
    apply (paid p o fit K b).expand
    · apply mul_le_mul_of_nonneg_right (wage_le kj Bn BV)
      unfold rowPrice
      exact div_nonneg (pow_nonneg rp.le _) (Finset.prod_nonneg (fun _ _ => pow_nonneg rp.le _))
    · exact pow_nonneg rp.le _
  obtain ⟨j,B,Bn,all⟩ := pool offer up source
  let const := (Fintype.card U : ℝ) * B^(Fintype.card t.Vertex)
  refine ⟨j,const,mul_nonneg (Nat.cast_nonneg _) (pow_nonneg Bn _),?_⟩
  have margins := eventually_all.mpr (fun v : t.Vertex =>
    Orbits.admissible_separated (I := t.Child v) F Q Mn ηp (cap t m D v))
  filter_upwards [small_scales (eventually_all.mpr all), small_scales margins,
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with r bank live small β β1 s x z adm
  obtain ⟨s0,sp,ratio,within⟩ := adm.2
  have ratio1 (i) := (ratio i).trans β1
  have under (v) : s v ≤ r := (scale_le_root t sp ratio1 v).trans_eq s0
  have fit (v) : WithinRoom (s v) M η (t.positions (v := v) x z) (z v) :=
    ⟨(within v).1, (within v).2⟩
  have opened (v) : orbitMargin Q.port (cap t m D v) (t.positions (v := v) x z) (z v) :=
    live (s v) (sp v) (under v) v _ _ (fit v) _ le_rfl
  let L (v : t.Vertex) := wage j B (s v)
  have Ln (v) : 0 ≤ L v := mul_nonneg Bn (pow_nonneg (zero_le_one.trans (shell_one _)) _)
  have costs (u : U) (v : t.Vertex) (K : Ortho) (b : Bool) :
      Priced (rawAt F Q t a x z u m c v K b) (publicAt F Q t a x z u m c v)
        (L v * port T t a u m c s v) (s v ^ (cap t m D v+1-(t.vertexChannel T u m c v).1)) :=
    bank (s v) (sp v) (under v) (u,v) _ _ (fit v) K b
  have per (u : U) (K : Ortho) (b : Bool) :
      ‖(∏ v, rawAt F Q t a x z u m c v K b) -
        (∏ i : Fin t.branches, publicAt F Q t a x z u m c i.succ) * rawAt F Q t a x z u m c 0 K b‖ ≤
        ((∏ v, L v) * attachedBase T t a s m) * t.cutoffGain D s := by
    rw [Fin.prod_univ_succ (fun v : t.Vertex => rawAt F Q t a x z u m c v K b), mul_comm]
    exact WilsonSharpPhysicalTreeEdgePowers.product T t a u m c s L sp (s0.trans_le small)
      ratio1 Ln _ _ _ (costs u 0 K b).left (fun i => costs u i.succ K b)
  have pay (K : Ortho) (b : Bool) :
      ‖contracted F Q t a x z D m c K b - held F Q t a x z D m c K b‖ ≤
        const * attachedBase T t a s m * (∏ v, shell (s v)^j) * t.cutoffGain D s := by
    unfold contracted held
    rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le ..).trans
    apply (Finset.sum_le_sum (fun (u : U) _ => per u K b)).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,L,wage,Finset.prod_mul_distrib,
      Finset.prod_const,const]
    ring
  refine ⟨pay,?_⟩
  rw [←root F Q t a x z D m c (opened 0)]
  apply difference _ _ pay
  · exact measurable_contracted F Q t a x z D m c opened
  · intro b
    unfold held
    exact integrable_finsetSum Finset.univ fun u _ =>
      (integrable_raw F Q m m c (t.positions (v := 0) x z) (t.childField T a u (v := 0))
        (z 0) (opened 0) b).const_mul (∏ i : Fin t.branches, publicAt F Q t a x z u m c i.succ)

end YM.Integration.WilsonSharpPhysicalTreeEdgeTelescope
