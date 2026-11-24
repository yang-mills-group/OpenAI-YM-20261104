import YM.MergeProof.West.Sushi
import YM.MergeProof.West.Teddy

/-! Restore the true engineering price of the untrimmed source on the
original heating receipt before bounding its finite ordinary product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickSurplus
open Lattice Wilson RG Labels Function Finset MvPolynomial
open Next.Rank Next.Rank.Glimmer Next.Rank.Particle Next.Rank.Atlas Next.Rank.Perch
open Next.Rank.Normal Next.Rank.Common Next.Rank.Rise Next.Rank.Configuration
open scoped BigOperators Classical
variable {G:Gauge}{n k d:ℕ}{V W:Type*}{g:Fin n→ℕ}
    {M:Fin n→V→(KeyIn G d⊕W)→₀ℂ}{P:Fin n→poly V}{F:Fin n→Label G d}

def cost (F:Fin n→Label G d):ℝ:=(∑ i,coin (thawKey (F i)))+1

theorem shelf (k n d:ℕ)(E b L s:ℝ)(income:E+L+3≤b):
    bill (b*d+E) s*bill (fuel k n) s^k≤bill (-L-2) s*bill b s^(d+1):=by
  rw [bills,bills,overlap,overlap]
  apply billed
  push_cast
  nlinarith only [fueled n k,income]

theorem retained {X:Spend n k}(B b L s:ℝ)(ms:Fin n→ℝ)
    (T:TollsX X g M P F (bill b s) (fun i=>bill (b*g i+ms i) s) (bill (fuel k n) s))
    (fees:∀i,ms i+L+3≤b):
    ∃ Y:Spend n k,Y.base=cost F ∧ Y.ξ=bill (-L-2) s ∧ Y.B=B ∧
      TollsX Y g M P F (bill b s) (fun i=>bill (b*g i+ms i) s) (bill (fuel k n) s):=by
  let ξ:=bill (-L-2) s
  let H:=cost F
  have nonneg (i:Fin n):0≤coin (thawKey (F i)):=Rise.sign _ _ zero_le_one
  have hc:1≤H:=le_add_of_nonneg_left (Finset.sum_nonneg fun i _=>nonneg i)
  let Y:Spend n k:=
    { ξ:=ξ
      base:=H
      pos:=(Real.exp_pos _).le
      home:=hc
      collision:=0
      B:=B
      cost:=(n:ℝ)*ξ*(H+ξ)^n * priced B (n*k)+H^n*(0*priced B (n*k))
      enough:=le_rfl }
  refine ⟨Y,rfl,rfl,rfl,⟨T.radius,T.base,T.words,?_,T.seats,T.renew,T.mark,fun i=>shelf k n (g i) (ms i) b L s (fees i)⟩⟩
  intro i
  exact (Finset.single_le_sum (fun j _=>nonneg j) (Finset.mem_univ i)).trans (le_add_of_nonneg_right zero_le_one)

open private vertices ceiling from YM.MergeProof.West.Teddy in
theorem original {X:Spend n k}{r b:ℝ}{a:Fin n→ℝ}(T:TollsX X g M P F r a b)
    (S:Finset (Fin n))(Q:Symmetric (Fin n × (KeyIn G d⊕W)))
    (μ:Fin n × (KeyIn G d⊕W)→ℂ)(paid:Sorts Q μ X.B):
    ‖blend Q μ (pot S (cast M P))-blend (ferry Q) (μ∘polar) (pot S (fun i=>thawKey (F i)))‖≤
      S.card*X.ξ*(X.base+X.ξ)^S.card*priced X.B (n*k):=by
  let B:=fun i=>rename (Sum.inl : KeyIn G d→_⊕W) (thawKey (F i))
  have hv i:totalDegree (cast M P i)≤k:=(ascent ..).trans (T.words i)
  have hb i:totalDegree (B i)≤k:=by dsimp only [B];rw [←T.mark i];exact (below_degree ..).trans (hv i)
  rw [←tide Q μ S (fun i=>thawKey (F i)),←map_sub]
  apply (Common.width _ (n*k) paid ?_).trans (mul_le_mul_of_nonneg_right (vertices T S) ?_)
  · rw [sub_eq_add_neg,show -(pot S B)=(-1:ℂ)•(pot S B) by simp]
    exact (totalDegree_add ..).trans (max_le (ceiling S _ hv) ((totalDegree_smul_le (-1:ℂ) _).trans (ceiling S B hb)))
  · have h:=paid.paid;dsimp only [priced];positivity

end YM.Integration.WilsonPhysicalThermalWickSurplus
end
