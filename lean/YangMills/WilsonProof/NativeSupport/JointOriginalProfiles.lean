import YangMills.WilsonProof.NativeSupport.JointOriginalNames
import YangMills.WilsonProof.NativeSupport.JointPrimitiveTests
import YangMills.WilsonProof.NativeSupport.FrozenAtoms
import YangMills.WilsonProof.NativeSupport.JointSkyScale
import YangMills.WilsonProof.NativeSupport.JointPhysicalPush

/-! Two distinct marks test the very same original choice and transition
bond. Microscopic fields are introduced exactly on their original date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Function Finset Lattice RG Wilson Marker MeasureTheory RGComparison.Core16 YM.Pressure
open Push.BetaTransport MergeProof.Accent Packet WilsonUniformUnmarkedInletEnergySites
open scoped Classical BigOperators
variable {G:Gauge} {A:Levels G} {I:Type} [Fintype I] [DecidableEq I] {t j N per:ℕ}
local notation "n₊" => A.S.side (j+1) per
local notation "n₀" => A.S.side j per
local notation "nᵁ" => A.S.side N per
local notation "S" => A.clock.op j per
def value (F:I → Config G (A.S.side N per) → ℝ) (h c:ℝ) (src:Sources I j N (A.S.side j per))
    (X:Config G (A.S.side (j+1) per)):ℂ:=
  match src with
  | .inl i=>((h*F i.val (i.property ▸ X):ℝ):ℂ)
  | .inr (true,_)=>((h*c:ℝ):ℂ)
  | .inr (false,_)=>((h:ℝ):ℂ)

def probe {n c₀:Side} (δ h c:ℝ) (σ:Bond c₀ → ℝ) (v:Names I t N n) (b:Bond c₀) (w:ℝ):ℝ:=
  match v with
  | .inl _=>1
  | .inr ((_,true),_)=>directionTest c (σ b) w
  | .inr ((_,false),_)=>thermalTest h δ w

variable (T:Slices A per) (tj:t ≤ j) (jn:j<N) (loc:I → Site (A.S.side N per))
variable (F:I → Config G (A.S.side N per) → ℝ)
omit [Fintype I] [DecidableEq I] in
theorem native_field (radius:ℕ) (h c:ℝ) (hp:0 ≤ h) (bill:1 ≤ c)
    (localF:∀ i,LocalOn (halo radius {loc i}) (F i)) (gauge:∀ i,GaugeInvariant (F i))
    (borel:∀ i,Measurable (F i)) (unit:∀ i X,|F i X| ≤ 1) (src:Sources I j N n₀) :
    let root:=place T loc jn (address T tj jn src)
    LocalOn (halo radius {root}) (value F h c src) ∧ GaugeInvariant (value F h c src) ∧
      Measurable (value F h c src) ∧ ∀ Z,‖value F h c src Z‖ ≤ h*c := by
  rcases src with i|⟨b,e⟩
  · obtain ⟨i,eq⟩:=i
    subst N
    have root:place T loc (le_refl _) (address T tj jn (.inl ⟨i,rfl⟩))=loc i := by
      simp only [place,traversal_self,home,origin,address,Sum.elim_inl,id_eq]
    change LocalOn (halo radius {place T loc (le_refl _) (address T tj jn (.inl ⟨i,rfl⟩))}) (fun X=>((h*F i X:ℝ):ℂ)) ∧ _
    rw [root]
    refine ⟨fun U Z eq=>congrArg (fun x:ℝ=>((h*x:ℝ):ℂ)) (localF i U Z eq),
      fun k X=>congrArg (fun x:ℝ=>((h*x:ℝ):ℂ)) (gauge i k X),?_,?_⟩
    · change Measurable (fun X=>((h*F i X:ℝ):ℂ))
      exact Complex.continuous_ofReal.measurable.comp (measurable_const.mul (borel i))
    · intro Z
      change ‖((h*F i Z:ℝ):ℂ)‖ ≤ _
      rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left ((unit i Z).trans bill) hp
  · cases b <;> refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,measurable_const,?_⟩
    · intro Z;change ‖(h:ℂ)‖ ≤ _;rw [Complex.norm_real,Real.norm_of_nonneg hp]
      exact le_mul_of_one_le_right hp bill
    · intro Z;change ‖((h*c:ℝ):ℂ)‖ ≤ _
      rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hp (zero_le_one.trans bill))]

omit [Fintype I] [DecidableEq I] in
theorem probe_borel {n c₀:Side} (δ h c:ℝ) (σ:Bond c₀ → ℝ) (v:Names I t N n) (b:Bond c₀):
    Measurable (probe δ h c σ v b) := by
  rcases v with i|⟨⟨_,k⟩,_⟩
  · exact measurable_const
  · cases k <;> unfold probe thermalTest directionTest <;> fun_prop

omit [Fintype I] [DecidableEq I] in
theorem probe_unit {n c₀:Side} {δ h c e:ℝ} (σ:Bond c₀ → ℝ) (δbill:2*(|δ| *c) ≤ h)
    (h0:0 < h) (h1:h ≤ 1) (cp:0 < c) (charge:∀ b,|σ b| ≤ 1)
    (e0:0 ≤ e) (ec:e ≤ c) (v:Names I t N n) (b:Bond c₀):‖probe δ h c σ v b e‖ ≤ 1 := by
  rcases v with i|⟨⟨_,k⟩,_⟩
  · exact (norm_one:‖(1:ℝ)‖=1).le
  · cases k
    · exact thermal_unit h0 h1 e0 ec δbill
    · exact direction_unit cp (charge b) e0 ec

omit [Fintype I] in
theorem physical_blank (i:{_i:I // j+1=N}):
    attached T tj jn (address (I:=I) T tj jn (.inl i))=∅ := by
  apply eq_empty_iff_forall_notMem.mpr;intro b hit
  obtain ⟨k,eq⟩:=(mem_filter.mp hit).2
  cases address_injective T tj jn eq

omit [Fintype I] in
theorem probe_on_cell (c h δ:ℝ) (σ:Bond n₀→ℝ) (b:Bond n₀) (k:(S).Choices) (X:Config G n₊) (Z:Config G n₀) :
    let read (flag:Bool):=address T tj jn (.inr (flag,b):Sources I j N n₀)
    let sig (flag:Bool):=JointPhysical.sample S k (attached T tj jn (read flag)) (probe δ h c σ (read flag)) X Z
    let e:=linkEnergy S (Z b*((S).prediction X k b)⁻¹)
    sig false=thermalTest h δ e ∧ sig true=directionTest c (σ b) e := by
  dsimp only
  simp only [JointPhysical.sample,attached_here,prod_singleton]
  exact ⟨rfl,rfl⟩

end YM.Integration.InletSusceptibility.Dated
