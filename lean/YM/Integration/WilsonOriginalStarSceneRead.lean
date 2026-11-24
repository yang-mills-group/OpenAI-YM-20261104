import YM.Integration.WilsonOriginalStarSceneRent
import YM.QuadraticLocal.Class.Foundry

/-! Uncut all-field identification of the registered reporting words and the original
section, before any flags or conditional integrations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarSceneRead
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open ActualRunCurvaturePackets NativeCurvatureTensor
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
  (d : V → ℕ) {n : Side} (o : V → Site n) (σ g τ : ℝ)
  (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ)

theorem nominal (i : Entry R d) (x : T) (U : Config G n) :
    (rows R d o σ g τ v t i).nominal g x U =
      t (root R d i) x * (g:ℂ)^(-(pole R d i:ℤ)) * scalar R d g τ v i *
         (((raw R d i).unmasked U (o (root R d i)):ℝ):ℂ) := by
  let a:=raw R d i
  let z:=normalizer a σ
  let j:=root R d i
  let b:=scalar R d g τ v i
  change ((z:ℂ)*b*t j x)*↑(g^(loan R d i).lag*(unitAtom a σ).unmasked U (o j))=_
  have shift : (unitAtom a σ).unmasked U (o j)=z⁻¹*a.unmasked U (o j):=evaluated a σ _
  rw [lag,shift,Complex.ofReal_mul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_zpow]
  have inverse : (z:ℂ)*(z:ℂ)⁻¹=1:=mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (positive a σ).ne')
  change _=t j x*(g:ℂ)^(-(pole R d i:ℤ))*b*↑(a.unmasked U (o j))
  linear_combination t j x*(g:ℂ)^(-(pole R d i:ℤ))*b*↑(a.unmasked U (o j))*inverse

theorem scalar_read (j : V) (x : T) (U : Config G n) :
    (rows R d o σ g τ v t (.inl j)).nominal g x U = t j x * v j 0 := by
  rw [nominal]
  simp [raw,rank,root,pole,scalar,Atom.unmasked,Atom.poly]

variable (N p k : ℕ)
set_option quotPrecheck false
local notation "gt" => Pert.Asymptotics.regulatorRun R.family N p k
local notation "pt" => (R.family.path.rep N p k).p.threshold
variable (h : k ≤ N) (sites : V → Site (R.family.side k p))

include h in
theorem monomials (j : V) (x : T) (U : Config G (R.family.side k p)) :
    (∑s:WilsonOriginalStarLaurentWallet.Socket R (d j),
      (rows R d sites σ gt pt v t (.inr ⟨j,s⟩)).nominal gt x U) =
      t j x * ActualRunPhysicalPages.kernel R N p k (d j) ((R.family.labels.level (d j)).core (v j)) (sites j) U := by
  let F:=R.family.labels.level (d j)
  let A:=ofRun R (d j)
  rw [Fintype.sum_sigma,run_kernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  let y:=(F.core (v j)) w
  let z:=ActualRunGradedKernels.rank R (d j) w
  let f (m : (Fin (A.data.count w) × G.ColorIndex) →₀ ℕ):=
      t j x * ((((pt⁻¹)^z:ℝ):ℂ)*y*MvPolynomial.coeff m (A.data.shape w)) *
        value (fun l=>(word m l).2) (fun l=>(A.data.columns w (word m l).1).atSite U (sites j))
  calc _ = ∑m:↥((A.data.shape w).support),f m.val:=by
         apply Finset.sum_congr rfl
         intro m _
         rw [nominal]
         change t j x*(gt:ℂ)^(-((WilsonOriginalStarLaurentWallet.lag R (d j) ⟨w,m⟩):ℤ)) *
           WilsonOriginalStarLaurentWallet.coefficient R (d j) gt pt (F.core (v j)) ⟨w,m⟩ *
             ↑((WilsonOriginalProjectedCurvatureAtom.atom _ _).unmasked U (sites j)) = _
         rw [mul_assoc (t j x),WilsonOriginalStarLaurentWallet.normalized R (d j) gt pt
           (ActualRunKernelPackets.regulator_pos R N p k h),WilsonOriginalProjectedCurvatureAtom.unmasked]
         rfl
       _ = ∑m∈(A.data.shape w).support,f m:=Finset.sum_coe_sort _ f
       _ = _ := by
         unfold basisValue
         rw [Finset.mul_sum,Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro m _
         dsimp only [f,y,z,A,F]
         ring

end YM.Integration.WilsonOriginalStarSceneRead
