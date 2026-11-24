import YM.Integration.WilsonSeparatedOriginalSlabWatchCorners

/-! Genuine support geometry of the signed common-centre coefficient, before every later fine stencil and volume. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchSupport
open Function Filter Set MeasureTheory Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits OPE.Cards
open MergeProof MergeProof.Accent Push.Local RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten Next.UVStress
open WilsonSeparatedOriginalSlabWatchCorners WilsonSeparatedOriginalSlabPhysicalBox
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {I:Type}[Fintype I] (W:Watch C)

def fixedSites:Fin W.n→E4:= C.S.gridPoint W.t ∘ W.x

def joined (x:Cloud I):Points (Fintype.card (Arms (I:=I) W)):=points (Sum.elim x (fixedSites W) ∘ runNames _)

def band (k:ℕ)(r:ℝ)(A:Set (Cloud I)):Set (Points (Fintype.card (Arms (I:=I) W))):=
  (fun p:E4×Cloud I=>joined W (fun i=>C.S.a k • p.1+r • p.2 i)) '' (Native.box ×ˢ A)

theorem wake {r:ℝ}(k:ℕ)(rp:0<r)(Ψ:Wave I)(g:Body)(v:Cloud I)(live:row C k r Ψ g v≠0):
    ∃z∈Native.box,∃y∈tsupport Ψ.val, v=fun i=>C.S.a k • z+r • y i:=by
  have witness:∃z∈Native.box, sheet C k r Ψ g v z≠0:=by
    by_contra! h;apply live;unfold row
    rw [setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet (fun z hz=>h z hz),integral_zero]
  obtain ⟨z,hz,hn⟩:=witness
  let y:Cloud I:=fun i=>r⁻¹ • (-(C.S.a k • z))+r⁻¹ • v i
  have hv:Ψ.val y≠0:=(mul_ne_zero_iff.mp hn).2
  refine ⟨z,hz,y,subset_tsupport _ hv,funext fun i=>?_⟩
  simp only [y,smul_add,smul_smul,mul_inv_cancel₀ rp.ne',one_smul];abel

theorem joined_continuous:Continuous (joined (I:=I) W):=by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i=>?_)
  change Continuous (fun v:Cloud I=>Sum.elim v (fixedSites W) (runNames _ i))
  cases runNames (Arms (I:=I) W) i with
  | inl a=>exact continuous_apply a
  | inr b=>exact continuous_const

theorem compact (k:ℕ)(r:ℝ)(A:Set (Cloud I))(hA:IsCompact A):IsCompact (band W k r A):=by
  apply (Pert.Cellular.cells_compact.prod hA).image
  apply (joined_continuous W).comp
  apply continuous_pi;intro i;fun_prop

theorem registered (k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(v:Cloud I)(A:Set (Cloud I))(enc:tsupport Ψ.val⊆A)
    (live:row C k r Ψ g v≠0):joined W v∈band W k r A:=by
  obtain ⟨z,hz,y,hy,present⟩:=wake k rp Ψ g v live
  exact ⟨(z,y),⟨hz,enc hy⟩,congrArg (joined W) present.symm⟩

/-- Actual watch coordinates (including the distinguished centre at zero) are pairwise distinct. -/
theorem distinct : Function.Injective (fixedSites W) ∧ ∀i:Fin W.n, fixedSites W i≠0:=by
  have hw:=generic_conf _ W.wild
  change Function.Injective (fun i:Fin (W.n+1)=>C.S.gridPoint W.t (Fin.cons (α:=fun _=>Cover) 0 W.x i)) at hw
  constructor
  · intro i j same
    change C.S.gridPoint W.t (W.x i)=C.S.gridPoint W.t (W.x j) at same
    have e:i.succ=j.succ:=hw (by simpa only [Fin.cons_succ] using same)
    simpa using e
  · intro i hi
    have e:i.succ=0:=hw (by simp only [Fin.cons_succ,Fin.cons_zero,show C.S.gridPoint W.t (0:Cover)=0 by ext a;change C.S.a W.t * ((0:ℤ):ℝ)=0;simp];exact hi)
    exact Fin.succ_ne_zero _ e

/-- Compactness and clearance may be chosen once, before the angular or cutoff data. -/
theorem separated (k:ℕ){r cap:ℝ}(rp:0<r)(thin:C.S.a k≤r)(A:Set (Cloud I))
    (separates:∀y∈A,Function.Injective y)(bounded:∀y∈A,∀i,‖y i‖≤cap)
    (exterior:∀j:Fin W.n,r+r*cap<‖fixedSites W j‖):band W k r A⊆conf _:=by
  rintro _ ⟨⟨z,y⟩,⟨hz,hy⟩,rfl⟩
  let x(i:I):=C.S.a k • z + r • y i
  have near:Function.Injective x:=by
    intro i j same;apply separates y hy
    have sm:r • y i=r • y j:=add_left_cancel same
    simpa only [smul_smul,inv_mul_cancel₀ rp.ne',one_smul] using congrArg (fun v:E4=>r⁻¹ • v) sm
  have far(i:I)(j:Fin W.n):x i≠fixedSites W j:=by
    have capI:‖x i‖≤r+r*cap:=by
      dsimp [x];calc ‖_+_‖≤‖C.S.a k • z‖+‖r • y i‖:=norm_add_le ..
        _ ≤ r+r*cap:=by grw [room_B (C:=C) z hz,thin,norm_smul,Real.norm_of_nonneg rp.le,bounded y hy i]
    exact fun h=>not_lt_of_ge (h ▸ capI) (exterior j)
  change Function.Injective (Sum.elim x (fixedSites W) ∘ runNames _)
  refine Function.Injective.comp ?_ (runNames _).injective
  rintro (i|i) (j|j) h
  · exact congrArg Sum.inl (near h)
  · exact (far i j h).elim
  · exact (far j i h.symm).elim
  · exact congrArg Sum.inr ((distinct W).1 h)

theorem room (cap:ℝ):∀ᶠ r:ℝ in 𝓝 0,∀j:Fin W.n,r+r*cap<‖fixedSites W j‖:=by
  apply eventually_all.mpr;intro j
  have h:Tendsto (fun r:ℝ=>r+r*cap) (𝓝 0) (𝓝 0):=by simpa using (tendsto_id.add (tendsto_id.mul_const cap) : Tendsto _ (𝓝 (0:ℝ)) _)
  exact h.eventually_lt_const (norm_pos_iff.mpr ((distinct W).2 j))

end YM.Integration.WilsonSeparatedOriginalSlabWatchSupport
