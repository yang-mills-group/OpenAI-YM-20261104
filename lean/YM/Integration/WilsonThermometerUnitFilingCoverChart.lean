import YM.Integration.WilsonThermometerUnitFilingCoverBasis

/-! An explicit finite coordinate domain for the indicated local cover field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverChart
open Function Lattice Gauge RG RegulatorIR Diagram Budget Budget.Packet Binding Prim Profiles Halo
open PertExtension.Series WilsonThermometerUnitFilingCoverBasis
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
abbrev patch (G:Gauge)(S:Finset Cover):Finset (Foot G):=(S×ˢ Finset.univ)×ˢ Finset.univ

def script (S:Finset Cover) (B:Portrait G) (z:Figure (↥(patch G S))):ℝ:=
  germ B z.1 (fill (placeFin (patch G S)) z.2)

def resident (B:Portrait G){h:ℕ}(good:LocalStamp B h)(S:Finset Cover)
    (inside:∀ t,LocalOn S (B t)):Prim.Run (germ B) where
  J:= ↥(patch G S)
  fin:=inferInstance
  inc:=placeFin (patch G S)
  script:=script S B
  smooth:=by
    apply good.people.neat
    intro i
    exact (G.exp_jet.contDiffAt.comp _ (((tall (patch G S) i).contDiffAt).comp
      (f:=Prod.snd) (0:Figure (↥(patch G S))) contDiffAt_snd)).of_le le_top
    exact contDiffAt_fst
    rfl
    have zero:fill (placeFin (patch G S)) 0=0:=(liftFill (placeFin (patch G S))).map_zero
    change win G (fill _ 0)=1
    rw [zero]
    ext1 i;change G.lieExp (0:G.Color)=_;simp
  reaches t v:=by
    apply inside t
    intro i hi _
    apply congr_arg G.lieExp
    ext1 j
    exact (fill_eq (patch G S) (i,j) (Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩,Finset.mem_univ _⟩) v).symm

def Centered (n:Side)(S:Finset Cover):Prop:=
  ∀ x∈S,∀ d,-(n.val:ℤ)<2*x d ∧ 2*x d≤n.val

theorem periodic (n:Side)(S:Finset Cover):∃ N:Side, n.val∣N.val ∧ Centered N S:=by
  let bound:ℕ:=∑ x∈S,∑ d:Axis, (2*x d).natAbs
  let N:Side:=n*⟨bound+1,by omega⟩
  have height:bound < N.val:=by
    change bound < n.val*(bound+1)
    have one:1≤n.val:=n.property
    apply Nat.lt_of_succ_le
    simpa only [Nat.succ_eq_add_one,one_mul] using Nat.mul_le_mul_right (bound+1) one
  refine ⟨N, dvd_mul_right ..,?_⟩
  intro x hx d
  have first:(2*x d).natAbs≤ ∑ i:Axis,(2*x i).natAbs:=
    Finset.single_le_sum (f:=fun i:Axis=>(2*x i).natAbs)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ d)
  have last:(∑ i:Axis,(2*x i).natAbs)≤bound:=
    Finset.single_le_sum (f:=fun y:Cover=>∑ i:Axis,(2*y i).natAbs)
      (fun _ _=>Nat.zero_le _) hx
  have hlt: (2*x d).natAbs < N.val:=lt_of_le_of_lt (first.trans last) height
  have abslt:|2*x d| < (N.val:ℤ):=by simpa using (Int.ofNat_lt.mpr hlt)
  exact ⟨(abs_lt.mp abslt).1,(abs_lt.mp abslt).2.le⟩

end YM.Integration.WilsonThermometerUnitFilingCoverChart
