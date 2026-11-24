import YM.Integration.WilsonOffsetJointRoster
import YM.Integration.WilsonOffsetSourceBasis
import YM.Integration.WilsonMeasuredRelativePair

/-! The independently tested microscopic pair on the actual Wilson cutoff
is the sum of complete genuinely planted rosters. The fine engineering costs
and the inverse of each physical transfer's terminal map are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetPhysicalPair
open Function Finset Lattice RG Wilson Source Labels Next.Foundations
open PhysicalNext.Repeat.Legato WilsonConditionalTaylorLabels WilsonOffsetJointRoster
open Marker Primitives.GCC.Anchor Comparison.RG02.Cumulants WilsonCumulantCommonOffset WilsonReportCashierConnected
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p d a b n k:ℕ}

def atom (N p:ℕ) {d:ℕ} (v:R.family.label d) (i:((frames G).level d).Index):ℂ:=
  let x:=(R.family.labels.level d).scaled (R.family.path.levels.clock.threshold N)⁻¹ ((R.family.factory d N p).terminal.symm v)
  ((R.family.S.a N:ℂ)^d)⁻¹*x i
def basis {n:Side} (i:((frames G).level d).Index) (x:Site n) (U:Config G n):ℂ:=
  (localSection G d).places (Pi.single i 1) x U
def two (i:((frames G).level a).Index) (j:((frames G).level b).Index):Roster G:=[⟨a,i⟩,⟨b,j⟩]
def seats {n:Side} (i:((frames G).level a).Index) (j:((frames G).level b).Index) (x y:Site n):Fin (two i j).length→Site n:=
  fun t=>if t.val=0 then x else y
def planted {n:Side} (i:((frames G).level a).Index) (j:((frames G).level b).Index) (x y:Site n) (U:Config G n):ℂ:=
  field (two i j) Finset.univ (seats i j x y) U

theorem literal {n:Side} (i:((frames G).level a).Index) (j:((frames G).level b).Index) (x y:Site n) (U:Config G n):
    planted i j x y U=basis i x U*basis j y U:=by
  unfold planted
  rw [finite]
  change (∏t:Fin 2,WilsonOffsetJointRoster.one (two i j) t (seats i j x y t) U)=_
  rw [Fin.prod_univ_two]
  rfl

theorem born (v:R.family.label d) (o:Site (R.family.side N p)) (U:Config G (R.family.side N p)):
    R.family.O N p v o U=∑i,atom R N p v i*basis i o U:=by
  let x:=(R.family.labels.level d).scaled (R.family.path.levels.clock.threshold N)⁻¹ ((R.family.factory d N p).terminal.symm v)
  let t:=((R.family.S.a N:ℂ)^d)⁻¹
  change t*(localSection G d).places x o U=_
  rw [WilsonOffsetSourceBasis.expand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change t*(x i*basis i o U)=(t*x i)*basis i o U
  ring

theorem relative (v:R.family.label a) (w:R.family.label b) (x y z:Site (R.family.side N p)) (U:Config G (R.family.side N p)):
    R.family.O N p v x U*(R.family.O N p w y U-R.family.O N p w z U)=
      ∑i,∑j,(atom R N p v i*atom R N p w j)*(planted i j x y U-planted i j x z U):=by
  rw [born R v x U,born R w y U,born R w z U,←Finset.sum_sub_distrib,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _
  rw [literal,literal]
  ring

theorem measured (Γ:Census (Fin n)) (hk:k≤N) (d:Fin n→ℕ) (v:(i:Fin n)→R.family.label (d i))
    (y:Fin n→Site (R.family.side N p)) (i j:Fin n) (ij:i≠j) (s:Γ.Mode) (hs:s.val={i,j}):
    let b:=anchored (C:=R.family) (N:=N) (p:=p) hk y
    displaced Γ hk d v y s=moment (R.family.beta N p) (fun U=>∑l,∑h,
      (atom R N p (v i) l*atom R N p (v j) h)*(planted l h (b i) (y j-(y i-b i)) U-planted l h (b i) (b j) U)):=by
  dsimp only
  rw [WilsonMeasuredRelativePair.held Γ hk d v y i j ij s hs]
  apply congrArg (moment _)
  funext U
  exact relative R (v i) (v j) _ _ _ U

end YM.Integration.WilsonOffsetPhysicalPair
