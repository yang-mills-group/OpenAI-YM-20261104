import YM.Integration.ActualWilsonFlagSwitch
import YM.MergeProof.Steps
import YM.MergeProof.Limb

/-! A two-replica determinant on the actual coarse forced Chainbook. Both copies have the
same complete coarse flag inventory. The interchange retains all independently selected
spectator sources and cancels every pair which does not join the two indicated marked sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonForcedReplicaBoundary
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open Merge MergeProof Palette Switch Ovens Progress.DirectedRecipe Mallow Refrain
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
open SectorNext.Vacuum ActualWilsonPacketSwitch
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {R : Rep G f} {W α μ reserve : ℝ} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}
    (H : Cash W α μ L Q o reserve T R) (U : Config G c)

-- The generic exchange imports use the classical equality on the label type.
local instance (priority := 2000) : DecidableEq H.Chainbook := Classical.decEq _

private theorem halves {n:Side} {J:Type*} (K:J→Support n) (T:Support n)
    (q:Finset J×Finset J) :
    (exchange K T q).1=mix K (region K T (q.1∪q.2)) q.1 q.2 ∧
    (exchange K T q).2=mix K (region K T (q.1∪q.2)) q.2 q.1 := ⟨rfl,rfl⟩

/-- Full mandatory inventory and the native compatibility and connectedness predicates. -/
def allowed (b : Finset H.Chainbook) : Prop := Letter.Valid H.bookFoot b ∧ H.eruptedPool U b

private theorem mix_allowed (s t : Finset H.Chainbook) (hs : allowed H U s) (ht : allowed H U t)
    (B : Support c) (cs : ∀r∈s,¬Disjoint (H.library r) B→H.library r⊆B)
    (ct : ∀r∈t,¬Disjoint (H.library r) B→H.library r⊆B) :
    allowed H U (mix H.library B s t) := by
  have disj:=ActualWilsonFlagSwitch.separate H.library B s t hs.1.disjoint ht.1.disjoint cs
  refine ⟨⟨Refrain.parted H disj,?_,disj⟩,?_⟩
  · intro r hr
    simp only [mix,ActualWilsonPacketSwitch.inner,outer,mem_union,mem_filter] at hr
    rcases hr with h|h
    · exact hs.1.classified _ h.1
    · exact ht.1.classified _ h.1
  · unfold Cash.eruptedPool
    ext z
    have fs:=Finset.ext_iff.mp hs.2 z
    have ft:=Finset.ext_iff.mp ht.2 z
    simp only [mem_biUnion] at fs ft
    simp only [mix,ActualWilsonPacketSwitch.inner,outer,mem_union,mem_filter,mem_biUnion]
    constructor
    · rintro ⟨i,h|h,hi⟩
      · exact fs.mp ⟨i,h.1,hi⟩
      · exact ft.mp ⟨i,h.1,hi⟩
    · intro hz
      by_cases near:z∈B
      · obtain ⟨i,his,hiz⟩:=fs.mpr hz
        exact ⟨i,Or.inl ⟨his,Finset.not_disjoint_iff.mpr ⟨z,H.shelf i hiz,near⟩⟩,hiz⟩
      · obtain ⟨i,hit,hiz⟩:=ft.mpr hz
        have remote:Disjoint (H.library i) B:=by
          by_contra meet
          exact near (ct i hit meet (H.shelf i hiz))
        exact ⟨i,Or.inr ⟨hit,remote⟩,hiz⟩

private theorem advance (a : Site c) (v : Finset H.Chainbook×Finset H.Chainbook)
    (hs : allowed H U v.1 ∧ allowed H U v.2) :
    allowed H U (exchange H.library {a} v).1 ∧ allowed H U (exchange H.library {a} v).2 := by
  let B:=region H.library {a} (v.1∪v.2)
  have C (i) (hi:i∈v.1∪v.2) : ¬Disjoint (H.library i) B→H.library i⊆B:=closed H.library {a} _ hi
  have C₁ r (hr:r∈v.1):=C r (mem_union_left _ hr)
  have C₂ r (hr:r∈v.2):=C r (mem_union_right _ hr)
  rw [(halves H.library {a} v).1,(halves H.library {a} v).2]
  exact ⟨mix_allowed H U _ _ hs.1 hs.2 B C₁ C₂,mix_allowed H U _ _ hs.2 hs.1 B C₂ C₁⟩

/-- Original forced occupation is preserved on both copies at the same actual field. -/
theorem gate (a : Site c) (v : Finset H.Chainbook×Finset H.Chainbook) :
    (allowed H U (exchange H.library {a} v).1 ∧ allowed H U (exchange H.library {a} v).2) ↔
    (allowed H U v.1 ∧ allowed H U v.2) :=
by
  refine ⟨fun k=>?_,advance H U a v⟩
  simpa only [involutive H.library {a} v] using advance H U a (exchange H.library {a} v) k

variable {ι : Type} [Fintype ι] (M : ι→Leaf R) (χ : Chi) (fee : ι→ℝ) (t : ℝ)
local notation "item" => fun (mask : Finset ι) (j : H.Chainbook)=>Palette.fete M H χ fee j U t mask

/-- A full signed original coarse forced configuration at a chosen finite source activation. -/
def term (mask : Finset ι) (q : Finset H.Chainbook) : ℝ :=
  if allowed H U q then ∏j∈q,(item) mask j else 0

/-- The genuine integrated forced component before its physical vacuum normalization. -/
def partition (mask : Finset ι) : ℝ := ∑'q,term H U M χ fee t mask q

theorem original (mask : Finset ι) (q : Finset H.Chainbook) :
    term H U M χ fee t mask q=H.canopyMill U (Palette.color M H χ U (Palette.ways fee t mask)) q := by
  by_cases valid:Letter.Valid H.bookFoot q ∧ H.eruptedPool U q
  · simp only [term,allowed,Cash.canopyMill,if_pos valid,Palette.fete]
  · simp only [term,allowed,Cash.canopyMill,if_neg valid]

private theorem split (B : Support c) (a b : Finset H.Chainbook) (v : H.Chainbook→ℝ) :
    (∏i∈mix H.library B a b,v i)=(∏i∈inner H.library B a,v i)*(∏i∈outer H.library B b,v i) := by
  unfold mix
  apply Finset.prod_union
  exact Finset.disjoint_left.mpr fun _ h k=>(mem_filter.mp h).2 (mem_filter.mp k).2

private theorem erase (d : ι) (x : Site c) (j : H.Chainbook)
    (atSite : x∈(M d).crest.image S.ratio.parent) (far : x∉H.library j)
    (p : Finset ι) (unused : d∉p) : (item) (insert d p) j=(item) p j := by
  simpa only [Finset.erase_insert unused] using Palette.limbs M H χ fee U d x atSite j far t (insert d p)

local notation "term₀" => term H U M χ fee t

/-- The full two-copy product difference at its true pair of configurations. -/
def difference (a b : ι) (x : Site c) (spectators : Finset ι)
    (q : Finset H.Chainbook×Finset H.Chainbook) : ℝ :=
  let q':=exchange H.library {x} q
  (term₀) (insert a (insert b spectators)) q.1*(term₀) spectators q.2-
    (term₀) (insert a spectators) q'.1*(term₀) (insert b spectators) q'.2

/-- Every potential contributor actually connects both native marked parent sites in the
overlap component of the combined two original labelled covers. -/
theorem disconnected (a b : ι) (hne:a≠b) (x y : Site c) (hx:x∈(M a).crest.image S.ratio.parent)
    (hy:y∈(M b).crest.image S.ratio.parent) (p : Finset ι) (ha:a∉p) (hb:b∉p)
    (q : Finset H.Chainbook×Finset H.Chainbook) (miss:y∉region H.library {x} (q.1∪q.2)) :
    difference H U M χ fee t a b x p q=0 := by
  let B:=region H.library {x} (q.1∪q.2)
  let s:=q.1;let u:=q.2
  have home:x∈B:=root_subset H.library {x} _ (mem_singleton_self x)
  have unhit (v : Finset H.Chainbook) (hv:v⊆s∪u) (i) (h:i∈inner H.library B v) : y∉H.library i :=
    fun z=>miss (closed H.library {x} _ (hv (mem_filter.mp h).1) (mem_filter.mp h).2 z)
  have away (v : Finset H.Chainbook) (i) (h:i∈outer H.library B v) : x∉H.library i :=
    fun z=>Finset.disjoint_left.mp (mem_filter.mp h).2 z home
  have gate₂:=gate H U x q
  by_cases good:allowed H U s ∧ allowed H U u
  · have both:=gate₂.mpr good
    dsimp only [difference]
    rw [(halves H.library {x} q).1,(halves H.library {x} q).2] at both ⊢
    change (term₀) (insert a (insert b p)) s*(term₀) p u-
      (term₀) (insert a p) (mix H.library B s u)*(term₀) (insert b p) (mix H.library B u s)=0
    have valid₁:allowed H U (mix H.library B s u):=both.1
    have valid₂:allowed H U (mix H.library B u s):=both.2
    simp only [term,if_pos good.1,if_pos good.2,if_pos valid₁,if_pos valid₂]
    have cut1:=(split H B s s ((item) (insert a (insert b p))))
    have cut2:=(split H B u u ((item) p))
    rw [same] at cut1 cut2
    rw [cut1,cut2,split H B s u ((item) (insert a p)),split H B u s ((item) (insert b p))]
    have left:(∏i∈inner H.library B s,(item) (insert a (insert b p)) i)=
        ∏i∈inner H.library B s,(item) (insert a p) i := by
      apply prod_congr rfl;intro i hi;rw [Finset.insert_comm]
      exact erase H U M χ fee t b y i hy (unhit s (Finset.subset_union_left) i hi)
        (insert a p) (by simp [hne.symm,hb])
    have right:(∏i∈outer H.library B s,(item) (insert a (insert b p)) i)=
        ∏i∈outer H.library B s,(item) (insert b p) i := by
      apply prod_congr rfl;intro i hi
      exact erase H U M χ fee t a x i hx (away s i hi) (insert b p) (by simp [hne,ha])
    have baseN:(∏i∈inner H.library B u,(item) (insert b p) i)=∏i∈inner H.library B u,(item) p i := by
      apply prod_congr rfl;intro i hi;exact erase H U M χ fee t b y i hy
        (unhit u Finset.subset_union_right i hi) p hb
    have baseF:(∏i∈outer H.library B u,(item) (insert a p) i)=∏i∈outer H.library B u,(item) p i := by
      apply prod_congr rfl;intro i hi;exact erase H U M χ fee t a x i hx (away u i hi) p ha
    rw [left,right,baseN,baseF];ring
  · have cut:¬(allowed H U (exchange H.library {x} q).1 ∧ allowed H U (exchange H.library {x} q).2):=gate₂.not.mpr good
    unfold difference term
    rcases not_and_or.mp good with n|n <;>rcases not_and_or.mp cut with m|m <;>
      simp [s,u] at n <;>simp [n,m]

variable (plot:Palette.Plot M H fee) {j k : ℕ} {e A B : ℝ} (bikes : Bikes Q L μ α A e B j k) (hB : 0≤B)

include plot bikes hB in
private theorem total (ht:t∈Set.Icc (0:ℝ) 1) (p : Finset ι) :
    Summable (fun q=>‖term H U M χ fee t p q‖) := by
  let charge:=Palette.bold M H fee k
  have pos (i):0≤charge i:=(Palette.fairs M H χ fee plot i k).rocket
  have bank:=summable_finsetProd_of_summable_nonneg pos (Palette.sizes M H χ fee plot bikes hB).1
  refine bank.of_nonneg_of_le (fun _=>norm_nonneg _) fun q=>?_
  by_cases h:allowed H U q
  · simp only [term,if_pos h,norm_prod]
    exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>(Palette.fairs M H χ fee plot i k).tasting U t ht p)
  · simp only [term,if_neg h,norm_zero];exact prod_nonneg fun i _=>pos i

local notation "P₀" => partition H U M χ fee t

include plot bikes hB in
/-- The full source determinant is the absolutely summed contribution of precisely the
connected two-copy forced configurations at the true unreplaced coarse flag inventory. -/
theorem joined (ht:t∈Set.Icc (0:ℝ) 1) (a b : ι) (hne:a≠b) (x y : Site c)
    (hx:x∈(M a).crest.image S.ratio.parent) (hy:y∈(M b).crest.image S.ratio.parent)
    (p : Finset ι) (ha:a∉p) (hb:b∉p) :
    let term':=fun q : Finset H.Chainbook×Finset H.Chainbook=>if y∈region H.library {x} (q.1∪q.2) then difference H U M χ fee t a b x p q else 0
    Summable term' ∧
      (P₀) (insert a (insert b p))*(P₀) p-(P₀) (insert a p)*(P₀) (insert b p)=∑'q,term' q := by
  intro term'
  let A:=(term₀) (insert a (insert b p))
  let B₀:=(term₀) p;let A':=(term₀) (insert a p);let B':=(term₀) (insert b p)
  let swap:=ActualWilsonFlagSwitch.order H.library {x}
  have hA:=total H U M χ fee t plot bikes hB ht (insert a (insert b p))
  have hB₀:=total H U M χ fee t plot bikes hB ht p
  have hA':=total H U M χ fee t plot bikes hB ht (insert a p)
  have hB':=total H U M χ fee t plot bikes hB ht (insert b p)
  have left:=summable_mul_of_summable_norm hA hB₀
  have right:=summable_mul_of_summable_norm hA' hB'
  let g:=fun z : Finset H.Chainbook×Finset H.Chainbook=>A' z.1*B' z.2
  have perm:(∑'z,g (swap z))=∑'z,g z:=swap.tsum_eq g
  have same q : A q.1*B₀ q.2-g (swap q)=term' q := by
    by_cases hit:y∈region H.library {x} (q.1∪q.2)
    · exact (if_pos hit).symm
    · exact (disconnected H U M χ fee t a b hne x y hx hy p ha hb q hit).trans (if_neg hit).symm
  refine ⟨(left.sub (right.comp_injective swap.injective)).congr same,?_⟩
  change (∑'z,A z)*(∑'z,B₀ z)-(∑'z,A' z)*(∑'z,B' z)=_
  rw [tsum_mul_tsum_of_summable_norm hA hB₀,tsum_mul_tsum_of_summable_norm hA' hB',←perm]
  exact (left.tsum_sub (right.comp_injective swap.injective)).symm.trans (tsum_congr same)
end YM.Integration.WilsonForcedReplicaBoundary
end
