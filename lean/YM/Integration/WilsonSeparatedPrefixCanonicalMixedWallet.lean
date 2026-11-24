import YM.Integration.WilsonSeparatedPrefixCanonicalCarton
import YM.Integration.WilsonSeparatedPrefixCanonicalFares

/-! Reserve a quarter on each of the original mixed catalogues at the very same cash
weights used to refile the one-site lamps and hard entries. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalMixedWallet
open Finset Function MeasureTheory Lattice Wilson RG Ac Marker Push GridApprox.Nil
open MergeProof MergeProof.Accent Extra.Histories
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V I Y:Type} [DecidableEq V] {J:Census V}
theorem smaller {w v:V → ℝ}{a e:ℝ}{B:ℕ}{S:I → Support n}{F:I → Y → Poly J}
    (actual:Towed w S F B e a)(paid:∀i,0≤v i)(within:∀i,v i≤w i):Towed v S F B e a:=by
  obtain ⟨fees,sum,roof,loc⟩:=actual
  refine ⟨fees,sum,roof,fun i=>?_⟩
  obtain ⟨sheet,pos,cover,charge⟩:=loc i
  refine ⟨sheet,pos,cover,le_trans ?_ charge⟩
  unfold wordsPrice
  apply Finset.sum_le_sum
  intro m _
  apply mul_le_mul_of_nonneg_right _ (pos m)
  apply Finset.prod_le_prod (fun i _=>paid i) (fun i _=>within i)

variable [Fintype V] {P:Rep G n} {o:V → Site n} {w v:V → ℝ} {e δ:ℝ}
  {h:V → Config G n → ℂ} {k:V → Box n → Config G n → ℂ}{F:Config G n → Poly J}
theorem original (stock:Served P h k F o w (e+δ) 1)(wp:∀i,0<w i)(vp:∀i,0<v i)
    (within:∀i,v i≤w i)(width:0≤δ)(wide:5≤P.p.B)
    (apart:∀a b:V,a≠b → P.p.B^2+1≤ separation (o a) (o b)):
    ∃H K,Carton o H K P.p.threshold ∧ F=restore P h k H K ∧
      ∀z:ℂ,4*‖z‖≤Real.exp (δ*(P.p.B/8:ℕ)) →
        Towed v id (fun Z U=>z • H Z U) P.p.B e (1/4) ∧
        Towed v Prod.fst (fun b U=>z • K b U) P.p.B e (1/4) := by
  obtain ⟨H,K,cart,hs,hk,eq⟩:=stock
  refine ⟨H,K,cart,eq,fun z cap=>?_⟩
  have cap':‖(4:ℂ)*z‖≤Real.exp (δ*(P.p.B/8:ℕ)):=by
    simpa only [norm_mul,Complex.norm_ofNat] using cap
  have reg:=WilsonSeparatedPrefixCanonicalMixed.salary width wp wide apart
    (fun Z=>(cart.exp Z).1.toBorne) (fun Z=>(cart.exp Z).2) hs (4*z) cap'
  have real:=WilsonSeparatedPrefixCanonicalMixed.salary width wp wide apart
    (fun b=>(cart.flag b).1.toBorne) (fun b=>(cart.flag b).2) hk (4*z) cap'
  have scale (v:Poly J):((4:ℂ)⁻¹) • ((4*z) • v)=z • v:=by
    rw [smul_smul,←mul_assoc]
    norm_num
  constructor
  · have stored:=smaller (WilsonSeparatedPrefixCanonicalFares.scale reg ((4:ℂ)⁻¹)) (fun i=>(vp i).le) within
    simpa only [scale,Function.id_def,norm_inv,Complex.norm_ofNat,mul_one,one_div] using stored
  · have stored:=smaller (WilsonSeparatedPrefixCanonicalFares.scale real ((4:ℂ)⁻¹)) (fun i=>(vp i).le) within
    simpa only [scale,Function.id_def,norm_inv,Complex.norm_ofNat,mul_one,one_div] using stored

end YM.Integration.WilsonSeparatedPrefixCanonicalMixedWallet
end
