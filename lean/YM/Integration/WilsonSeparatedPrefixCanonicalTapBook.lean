import YM.Integration.WilsonSeparatedPrefixCanonicalMixedWallet
import YM.Integration.WilsonSeparatedPrefixCanonicalZeroPost
import YM.Integration.WilsonSeparatedPrefixCanonicalPolynomial

/-! The whole authentic physical mixed register and each original hard singleton are
successively amplified on the same full roster, keeping the actual masked regular fields. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalTapBook
open Finset Function Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open Extra.Histories Extra.Multi Extra.Trajectories Lodestar
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V][Fintype V]
  (P:Rep G n)(o:V → Site n)(φ:V → Config G n → ℂ)(h:V → Box n → Config G n → ℂ)
  (F:Config G n → Poly (Marks V))(w₀ w:V → ℝ)(e δ:ℝ)
  (M:V → Support n → Config G n → Poly (Marks V))(m k:V → ℝ)
def reg (U:Config G n)(Z:Support n):Poly (Marks (V×Bool)):=∑v,duplicate V (M v Z U)
def hard (K:Box n → Config G n → Poly (Marks V))(b:Box n)(U:Config G n):Poly (Marks (V×Bool)):=
  duplicate V (Mach (Marks V) (fun v=>h v b U)+K b U)

theorem original (stock:Served P φ h F o w₀ (e+δ) 1)(wp:∀v,0<w v)(pos:∀v,0<w₀ v)
    (within:∀v,w v^2≤w₀ v)(width:0≤δ)(wide:5≤P.p.B)
    (apart:∀a b:V,a≠b → P.p.B^2+1≤ separation (o a) (o b))
    (loc:∀v Z,Burns o Z (M v Z) P.p.threshold)
    (flag:∀v b,Flow o b (fun U=>Poly.send ((Marks V).fire v) (h v b U)) P.p.threshold)
    (wages:∀v,Towed (fun i=>w i^2) id (M v) P.p.B e (m v))
    (keys:∀v,Towed (fun i=>w i^2) Prod.fst (fun b U=>Poly.send ((Marks V).fire v) (h v b U)) P.p.B e (k v))
    (room:(∑v,m v)+1/4≤1):
    ∃H K,Carton o H K P.p.threshold ∧ F=restore P φ h H K ∧
      (∀Z U,(duplicate V (H Z U)).part (Marks (V×Bool)).quiet=0) ∧
      (∀b U,(hard h K b U).part (Marks (V×Bool)).quiet=0) ∧
      ∀z:ℂ,4*‖z‖≤Real.exp (δ*(P.p.B/8:ℕ)) → (∑v,‖z‖*k v)+1/4≤1 →
        Served P (fun (_:V×Bool) _=>0) (fun (_:V×Bool) _ _=>0)
          (WilsonSeparatedPrefixCanonicalPolynomial.source P (fun Z U=>reg M U Z)
            (fun Z U=>duplicate V (H Z U)) 0 (hard h K) z) (o ∘ Prod.fst) (w ∘ Prod.fst) e 1 := by
  obtain ⟨H,K,cart,field,pay⟩:=WilsonSeparatedPrefixCanonicalMixedWallet.original stock pos
    (fun i=>sq_pos_of_pos (wp i)) within width wide apart
  refine ⟨H,K,cart,field,fun Z U=>?_,fun b U=>?_,fun z cap funded=>?_⟩
  · rw [←two_quiet,seal_part]
    exact hop _ _ ((cart.exp Z).2 U)
  · unfold hard
    rw [←two_quiet,seal_part,Poly.part_plus,mach_quiet,hop _ _ ((cart.flag b).2 U),add_zero]
  · obtain ⟨soft,forced⟩:=pay z cap
    have issue:=WilsonSeparatedPrefixCanonicalZeroPost.original P w wp M h
      (WilsonSeparatedPrefixCanonicalCarton.rescale cart z) loc flag soft forced wages keys z room funded
    convert issue using 1
    unfold WilsonSeparatedPrefixCanonicalPolynomial.source reg hard
    funext U
    congr 2
    · funext Z W
      simp only [map_smul]
    · funext b W
      simp only [Pi.zero_apply,zero_add,map_add,smul_add,Mach,map_sum,Finset.smul_sum,map_smul]

end YM.Integration.WilsonSeparatedPrefixCanonicalTapBook
end
