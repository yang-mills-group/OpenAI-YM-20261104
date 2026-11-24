import YM.Integration.WilsonPointChildDeckLift
import YM.Integration.WilsonOriginalRelativePageTail
import YM.Integration.WilsonPointChildFoldedPageIncome
import YM.Integration.WilsonPointChildNamedRootSum
import YM.WilsonCoeffUV.Marked.Capture.Draw
import YM.Integration.WilsonPointChildPlacedFold
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildDeckAngular
open YM Lattice WilsonCoeffUV RG FormalBulk08 Laurent
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open Work.F08 Function Finset Filter
open scoped Classical BigOperators Topology
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail
variable {ι α:Type} [DecidableEq ι] {n X:Side}


variable {V:Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def window {r:ℕ}(root:Site X)(x:dock (Site X) α r):ℝ:=
  (Syn (tor X) (fun _:Unit=>root) {()} x:ℕ)

omit [DecidableEq ι] in
theorem included (I:Finset ι)(o:ι)(live:o∈I)(root:Site X)(G:ι→Site X)(home:G o=root)
    (r:ℕ)(x:dock (Site X) α r):window root x ≤ Syn (tor X) G I x:=by
  let u:(↑({()}:Finset Unit)⊕Fin r) → (I ⊕ Fin r):=Sum.elim (fun _=>Sum.inl ⟨o,live⟩) Sum.inr
  have film:∀v,foyer (fun _:Unit=>root) {()} x v=foyer G I x (u v):=by
    intro v;cases v with
    | inl v=>exact home.symm
    | inr v=>rfl
  change ((league (tor X) (foyer (fun _:Unit=>root) {()} x)):ℝ) ≤ _
  exact_mod_cast league_le (tor X) (foyer (fun _:Unit=>root) {()} x) (fun i j=>by
    rw [film i,film j];exact leg_le (tor X) (foyer G I x) (u i) (u j))

theorem wage [Fintype α][DecidableEq α] (h:n.val∣X.val)(I:Finset ι)(o:ι)
    (root:Site X)(site:(I.erase o) → Site X)(r:ℕ)(w M:ℝ)(hw:0≤w)
    (K:(ι → Cover)→dock Cover α r→V)(test:V →L[ℝ] ℂ)
    (earned:SumBudget (fun q:Fence α I o r=>
      Real.exp (w*Syn terrain (toe I o (lift root) q.1) I q.2)*‖K (toe I o (lift root) q.1) q.2‖) M):
    let G:=fun p=>toe I o (lift root) (WilsonPointChildDeckLift.centers h I o site p)
    let row:=fun p x=>test (plume (K (G p)) X x)
    ∑p,∑x, Real.exp (w*(Syn (tor X) (wrap X ∘ G p) I x:ℝ))*‖row p x‖ ≤ ‖test‖*M:=by
  intro G row
  let span:=fun p (x:dock (Site X) α r)=>(Syn (tor X) (wrap X ∘ G p) I x:ℝ)
  have born:=WilsonPointChildFoldedPageIncome.original I o (lift root) r X
    (WilsonPointChildDeckLift.centers h I o site) (WilsonPointChildDeckLift.injective h I o site) K hw earned
  change ∑p,∑x, Real.exp (w*span p x)*‖row p x‖ ≤ ‖test‖*M
  refine le_trans ?_ (mul_le_mul_of_nonneg_left born (norm_nonneg test))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _=>by
      change Real.exp (w*span p x)*‖test (plume (K (G p)) X x)‖≤‖test‖*(_*‖plume (K (G p)) X x‖)
      calc
        _≤Real.exp (w*span p x)*(‖test‖*‖plume (K (G p)) X x‖):=mul_le_mul_of_nonneg_left (test.le_opNorm _) (Real.exp_pos _).le
        _= _:=by ring

private theorem tail {J Z:Type} [dec:DecidableEq J][Fintype J][Fintype Z](h:n.val∣X.val)(root:Site X)(site:J → Site X)
    (row:(J → Fin (Pages n X)) → Z → ℂ)(span:(J → Fin (Pages n X)) → Z → ℝ)(out:Z → ℝ)
    {w D M:ℝ}(hw:0≤w)(near:∀j,(separation root (site j):ℝ)≤D)
    (paths:∀p x j,(separation root (locate h site p j):ℝ)≤ span p x)
    (output:∀p x,out x≤ span p x)(fee:∑p,∑x,Real.exp (w*span p x)*‖row p x‖≤M):
    (∑x,Real.exp (w*out x/2)*‖(∑p,row p x)-row (retained h site) x‖)≤
      Real.exp (-(w*((n.val:ℝ)-D))/2)*M:=by
  obtain rfl : dec=fun a b:J=>Classical.propDecidable (a=b) := Subsingleton.elim _ _
  have total:=WilsonOriginalRelativePageTail.original h root site row span out (ρ:=w) (D:=D) (d:=0) hw near paths
    (fun p x=>(output p x).trans_eq (add_zero _).symm) fee
  rwa [sub_zero] at total

attribute [local irreducible] Finset.erase
theorem original [Fintype α][DecidableEq α] (h:n.val∣X.val)(I:Finset ι)(o:ι)(live:o∈I)
    (root:Site X)(site:(I.erase o) → Site X)(r:ℕ)(w D M:ℝ)(hw:0≤w)
    (K:(ι → Cover)→dock Cover α r→V)(test:V →L[ℝ] ℂ)
    (near:∀j,(separation root (site j):ℝ)≤D)
    (earned:SumBudget (fun q:Fence α I o r=>
      Real.exp (w*Syn terrain (toe I o (lift root) q.1) I q.2)*‖K (toe I o (lift root) q.1) q.2‖) M):
    let G:=fun p=>toe I o (lift root) (WilsonPointChildDeckLift.centers h I o site p)
    let row:=fun p x=>test (plume (K (G p)) X x)
    (∑x,Real.exp (w*window root x/2)*‖(∑p,row p x)-row (retained h site) x‖)≤
      Real.exp (-(w*((n.val:ℝ)-D))/2)*(‖test‖*M):=by
  intro G row
  let span:=fun p (x:dock (Site X) α r)=>(Syn (tor X) (wrap X ∘ G p) I x:ℝ)
  have price:=wage h I o root site r w M hw K test earned
  have paths:∀p x j,(separation root (locate h site p j):ℝ) ≤ span p x:=
    fun p x j=>Nat.cast_le.mpr (WilsonPointChildDeckLift.connected h I o live root site r p x j)
  have inside:∀p x,window root x ≤ span p x:=fun p x=>
    included I o live root (wrap X ∘ G p) (by simp [G,toe]) r x
  have finished:=tail h root site row span (window root) (M:=‖test‖*M) hw near paths inside price
  exact finished

end YM.Integration.WilsonPointChildDeckAngular
