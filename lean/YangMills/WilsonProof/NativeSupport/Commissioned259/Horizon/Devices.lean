import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Payments
/-!
# Allow physical multi-moments at varying vector prices. Compatibility & multilinearity

`nearResponse` with weights of actual labels. Include arbitrary label budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Filter Set Asymptotics MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
variable {G:Gauge}{L:Register G} {S:Table L} {Q:DiffPlan S} {C:Family G}
    {I J : Type} [Fintype I] [Fintype J] {d:I→ℕ} {e:J→ℕ} {V : Type*} {l : Filter V}

abbrev Oper {E:Type*}[AddCommGroup E][Module ℂ E] (S:Table L)(d:I→ℕ) := MultilinearMap ℂ (fun i=>S.Field (d i)) E
-- easier with explicit E

/-- Extend by buying all fixed basis tuples. Need no pricing off conf -- tasks remain
true layouts, point functions totalized only for Lean. -/
lemma depends {E:Type*}[NormedAddCommGroup E] [NormedSpace ℂ E] {r w:V→ℝ} (h:Tendsto r l (𝓝[>] 0))
    (X:V→ Oper (E:=E) S d) (u:V→Labels S d) (f:I→V→ℝ)
    (B : ∀ (g:Labels S d), Allowance l r w (fun v=>X v g))
    (hu:∀ i,Allowance l r (f i) (fun v=>u v i)) : Allowance l r (fun v=>(∏ i, f i v)* w v) (fun v=> X v (u v)) := by
  let b i:= Module.finBasis ℂ (S.Field (d i)); let c k i j:= LinearMap.toContinuousLinearMap ((b i).coord j) (u k i)
  let Z := ∀ i, Fin (Module.finrank ℂ (S.Field (d i)))
  haveI : Fintype Z := inferInstanceAs (Fintype (∀ i, Fin (Module.finrank ℂ (S.Field (d i)))))
  have h0 (i:I) (k:V) : u k i = ∑ j, c k i j • b i j := Eq.symm (Module.Basis.sum_repr (b i) (u k i))
  have he (k:V) : X k (u k) = ∑ z:Z, (∏ j, c k j (z j)) • X k (fun j=> b j (z j)) := by
    nth_rw 1 [show u k=(fun i=>∑ j, c k i j • b i j) from funext fun i=>h0 i k]
    refine ((X k).map_sum (fun i j=> c k i j • b i j)).trans (Finset.sum_congr (by ext; simp only [Finset.mem_univ]) fun i _=> (X k).map_smul_univ _ _)
  simp_rw [he]
  exact Allowance.sum h _ _ fun z _=> Allowance.smul (Allowance.prod _ (fun i _=>Allowance.linear (LinearMap.toContinuousLinearMap _) (hu i))) (B _)

lemma variate {E : Type*} [NormedAddCommGroup E][NormedSpace ℂ E] {r w : V→ℝ} (h:Tendsto r l (𝓝[>] 0)) (X:V→Oper (E:=E) S d) (u:V→Labels S d)
    (b : ∀ g:Labels S d,Allowance l r w (fun v=>X v g)) (hc : ∀ i,Allowance l r (fun _=>1) (fun v=> u v i)) :
    Allowance l r w (fun v=> X v (u v)) := by simpa only [Finset.prod_const_one,one_mul] using depends h X u (fun _ _=>1) b hc

/-- Genuine Physical continuum full. -/
def whole₁ (T : Table L) (x:I→E4) (y:J→E4) : Oper (E:=Oper (E:=ℂ) S e) S d :=
    (moment (S:=S) T (d:=Sum.elim d e) (beside x y)).currySum
lemma whole₁_eq (T:Table L) (x:I→E4) (u:Labels S d)(y:J→E4)(v:Labels S e) :
    Orbits.whole T x u y v = whole₁ T x y u v := by
  erw [Orbits.whole, whole₁,MultilinearMap.currySum_apply]; congr 1; funext i; cases i <;> rfl

def distance (T:Table L) (x:I→E4) (u:Labels S d) (m : ℕ) (z:S.Field m) (o:E4) (y:J→E4) : Oper (E:=ℂ) S e :=
    whole₁ T x y u - whole₁ T (d:=fun (_:Unit)=>m) (sole o) y (sole z)
lemma far_distance (T:Table L) {m : ℕ} (z:S.Field m) (x:I→E4) (u:Labels S d)(y:J→E4)(v:Labels S e) (o:E4):
    discrepancy T m x o u z y v=distance T x u m z o y v := by
  change Orbits.whole _ _ _ _ _ - Orbits.whole _ _ _ _ _= _; simp_rw [ whole₁_eq ]; rfl

def oldN (P:Prescription Q)(x:I→E4)(o:E4)(n:ℕ) : Oper (E:=S.Field n) S d :=
    ∑ i∈bands Q n,(Orbits.checkRow P i x o).smulRight (P.loaded i n)
lemma oldN_eq (hS:S.Hierarchy)(P:Prescription Q)(x:I→E4)(o:E4)(n:ℕ)(u:Labels S d):
    shadowOld P n x o u=oldN P x o n u := by simp_rw [oldN,_root_.sum_apply,MultilinearMap.smulRight_apply, Orbits.check_eq P _ hS]; rfl

variable {X:S.Rotation}{ρ:S.RealSpin}

def packetN (Q':Reader Q X ρ) (x:I→E4)(o:E4)(n:ℕ) : Oper (E:=S.Field n) S d :=
    ∑ j:Fin (n+1), (Q.rise (Nat.le_of_lt_succ j.isLt)).compMultilinearMap (Q'.fresh j x o)
lemma packetN_eq (Q':Reader Q X ρ)(x:I→E4)(o:E4)(n:ℕ)(u:Labels S d): Q'.packet n x u o=packetN Q' x o n u := by rw [packetN,_root_.sum_apply]; rfl
-- Near discrepancy (Far fixed) from a single MLA of c
abbrev local_disc (T:Table L)(x:I→E4)(m:ℕ)(F:Oper (E:=S.Field m) S d)(y:J→E4)(v:Labels S e)(o:E4) : Oper (E:=ℂ) S d :=
    (show Oper (E:=ℂ) S d from sectionLabels (d:=Sum.elim d e) v (moment T (d:=Sum.elim d e) (S:=S) (beside x y))) - (upon T m o y v).compMultilinearMap F
lemma location (T:Table L)(x:I→E4)(m:ℕ)(F:Oper (E:=S.Field m) S d)(y:J→E4)(v:Labels S e)(o:E4)(u:Labels S d) :
    discrepancy T m x o u (F u) y v= local_disc T x m F y v o u := by
    unfold local_disc discrepancy; erw [MultilinearMap.sub_apply, sectionLabels_apply]; rfl
end YM.OPE.Flash259HorizonFork
