import YM.FVA2.Vertices
/-!
# The full orbit log Haar reading into the FP slot alphabet

Normalized relative Jacobian vs accepted MS log(Haar) stencil. Exact in every jet.
The determinant contribution of the section, which is *not* counted the same
way in `weightH`, is proved via ghost pairings next.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.PairCoords
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Chart PertExtension.Orb
open Function Filter Metric MeasureTheory TreeBasis Trans
open Wilson Based GaussianScore MS.Orbit MS MS.Orbit.Cog MS.Swirl Green MS.Bare MS.Plane MS.Landau MS.Koszul
open Modes MS.Native MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Native.Draft MS.Native.Wilsonian MS.Native.Chart MS.Puff MS.Puff.Engine MS.Puff.Mom MS.Book MS.Book.Program Precision Finset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {U J:Type} {n:Side}
variable (m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n))
variable (he:_root_.Even n.val)

-- orbit sum. note no fixed unoriented links. subtype equiv count
include he
lemma coverTwice (f:Edge (Site n)→ℝ)(h: ∀ i,f (Orb.reflect i)=f i):
    ∑ i: Edge (Site n),f i = 2*(∑ i:Orb.OEdge n, f i.val):= by
   let τ (u: OEdge n ⊕ OEdge n) : Edge (Site n) := Sum.elim (fun i:OEdge n=>i.val) (fun i:OEdge n=>Orb.reflect i.val) u; have ht : Bijective τ:= by
      constructor
      · intro i j hj; rcases i with a|a <;> rcases j with b|b
        · exact congr_arg _ (Subtype.ext hj)
        · change a.val = Orb.reflect b.val at hj
          have hu : a.val=b.val:=by rw [← a.property,hj,eR_reflect,b.property]
          exact (no_fixed_edge he b.val (hj.symm.trans hu)).elim
        · change Orb.reflect a.val=b.val at hj
          have hu:b.val=a.val:=by rw [← b.property, ← hj,eR_reflect,a.property]
          exact (no_fixed_edge he a.val (hj.trans hu)).elim
        · exact congr_arg _ (Subtype.ext (( Involutive.injective (f:= Orb.reflect) Orb.reflect_reflect ) hj))
      intro x; rcases Orb.eR_spec x with H|H
      exact ⟨.inl ⟨_,H⟩,rfl⟩
      exact ⟨.inr (Orb.index x), (congr_arg Orb.reflect H).trans (Orb.reflect_reflect _)⟩
   rw [← Equiv.sum_comp (Equiv.ofBijective τ ht) f, Fintype.sum_sum_type]; simp_rw [ Equiv.ofBijective_apply]; change (∑ i:OEdge n,f i.val)+(∑ i:OEdge n,f (Orb.reflect i.val))= _; simp_rw [h,two_mul]

variable (Z: ChartRatio G) (hp:LocalRatio Z)

omit he in
/-- top relative link measure, physical orbit coordinates (per-link J(0)=1). -/
abbrev haar (G:Gauge)(n:Side)(Z:ChartRatio G)(x:Wilson.Field G n):= TreeBasis.density (Orb.OEdge n) Z ((plan G n).L x)
include hp
lemma volume_charge : MS.Native.Chart.totalH (P:=Site n) (G:=G) ∘ LMap G n =ᶠ[𝓝 0] fun x=>2*Real.log (haar G n Z x):= by
    let Y:=fun x:Wilson.Field G n=> (plan G n).L x; have ht:Tendsto Y (𝓝 0) (𝓝 0):= by simpa using (plan G n).L.continuous_of_finiteDimensional.tendsto 0
    have he': Tendsto (LMap G n) (𝓝 0) (𝓝 0):= by simpa using (LMap G n).continuous.tendsto 0
    filter_upwards [he'.eventually (Filter.eventually_all.mpr (fun i:Edge (Site n)=> ((continuous_apply i).tendsto (0: Lot G (Edge (Site n)))).eventually Maurer.opposite)), ht.eventually (Filter.eventually_all.mpr (fun i:OEdge n=> ((continuous_apply i).tendsto (0:Cone G n)).eventually ((Maurer.real_ratio hp).and (show ∀ᶠ t:G.Color in 𝓝 0,0 < LocalH.spin G t from Maurer.lives G))))] with x hx hX
    change ∑ i:Edge (Site n), Maurer.lac ((coverL G n (Y x)) i)=_
    have hh (i:OEdge n): Z.J (Y x i)=LocalH.spin G (Y x i)∧0 < LocalH.spin G (Y x i):= hX i
    rw [ coverTwice he _ (fun i:Edge (Site n)=>?_), haar, TreeBasis.density, Real.log_prod ]; rotate_left
    · intro i _; exact (hh i).1.symm ▸ (hh i).2.ne'
    · rw [cover_reflect G n he]; exact hx i
    congr 1; apply Finset.sum_congr rfl; intro i _; rw [coverL_at]; unfold Maurer.lac; exact congr_arg Real.log (hh i).1.symm
omit he in
lemma haar_analytic : ContDiffAt ℝ ω (haar G n Z) 0:=by unfold haar; apply ContDiffAt.comp (g:=TreeBasis.density (Orb.OEdge n) Z) (f:=(plan G n).L.toContinuousLinearMap) _ _ (plan G n).L.toContinuousLinearMap.contDiff.contDiffAt; rw [map_zero]; exact density_hot Z hp
omit he in
lemma haar_one : haar G n Z 0=1:= by rw [haar,map_zero]; exact density_zero Z hp
omit he in
lemma log_analytic : ContDiffAt ℝ ω (fun x=>Real.log (haar G n Z x)) 0:= (haar_analytic (n:=n) Z hp).log (by rw [haar_one Z hp]; norm_num)

theorem plug_haar : plug (mkPlug m b) (pay true • docket n (Wilsonian.H G)) = ink (bell m) (fun x=>Real.log (haar G n Z x)) := by
   rw [map_smul,Wilsonian.shiftD,show ink (glow G (Site n)).e0 totalH=reads totalH from rfl,pin_read m b Native.Chart.nice_totalH];
   let U':=fun x=>Real.log (haar G n Z x)
   rw [show ink (bell m) (totalH (P:=Site n) ∘ LMap G n) = ink (bell m (J:=J)) ((2:ℝ) • U') from inkit _ (volume_charge he Z hp), ink_smul _ (show germ U' from log_analytic Z hp), smul_smul, show pay true * ((2:ℝ):ℂ)=1 from (by unfold pay; norm_num), one_smul]
end YM.FVA2.PairCoords
