import YM.Integration.WilsonSeparatedPrefixCanonicalMixed
import YM.Integration.WilsonThermometerWeakReflectedRows

/-! Mode-by-mode admission on the measured Wilson representation at its actual
last-separated cut. The original singleton profiles and quiet gas are fixed. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalCarton
open Function Finset Set MeasureTheory Lattice Wilson RG Marker MergeProof Accent Push.GridApprox.Nil
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {J:Census V}
  {o:V→Site n} {q:ℝ}

private theorem bore {Z:Support n}{g:Config G n→Poly J}(entry:Borne o Z g q)(z:ℂ):
    Borne o Z (fun U=>z • g U) q := by
  constructor
  · exact fun A B e f=>congrArg (z • ·) (entry.home A B e f)
  · exact fun h U=>congrArg (z • ·) (entry.turns h U)
  · exact fun i=>measurable_const.mul (entry.me i)
  · intro U s missing
    rw [Poly.part_smul,entry.scope U s missing,mul_zero]

private theorem rises_smul (z:ℂ){g:Poly J}(raised:rises g):rises (z • g) := by
  intro s nonzero
  apply raised s
  exact fun e=>nonzero (by rw [Poly.part_smul,e,mul_zero])

theorem rescale {H:Support n → Config G n→Poly J} {K:Box n → Config G n→Poly J}
    (existing:Carton o H K q) (z:ℂ) :
    Carton o (fun Z U=>z • H Z U) (fun b U=>z • K b U) q := by
  constructor
  · intro Z
    obtain ⟨entry,modes⟩:=existing.exp Z
    refine ⟨⟨bore entry.toBorne z,fun U h=>entry.permits U (fun eq=>h (by rw [eq,smul_zero])),fun U=>?_⟩,
       fun U=>rises_smul _ (modes U)⟩
    rw [Poly.part_smul,entry.sil U,mul_zero]
  · intro b
    obtain ⟨entry,modes⟩:=existing.flag b
    exact ⟨⟨bore entry.toBorne z,fun U h=>entry.permits U (fun eq=>h (by rw [eq,smul_zero]))⟩,
       fun U=>rises_smul _ (modes U)⟩

theorem original [Fintype V] (P:Rep G n) {L:V → Config G n→ℂ} {h:V→Box n → Config G n→ℂ}
    {F:Config G n→Poly J}{w:V→ℝ}{e δ A:ℝ} (stock:Served P L h F o w (e+δ) A)
    (w₀:∀v,0<w v) (hδ:0≤δ) (hB:5≤P.p.B)
    (apart:∀v u:V,v≠u → P.p.B^2+1 ≤ separation (o v) (o u)) :
    ∃H K, Carton o H K P.p.threshold ∧
      F=restore P L h H K ∧
      ∀z:ℂ,‖z‖≤Real.exp (δ*(P.p.B/8:ℕ)) →
        Served P L h (restore P L h (fun Z U=>z • H Z U) (fun b U=>z • K b U)) o w e A:=by
  obtain ⟨H,K,cart,soft,hard,eq⟩:=stock
  refine ⟨H,K,cart,eq,fun z cap=>⟨_,_,rescale cart z,?_,?_,rfl⟩⟩
  · exact WilsonSeparatedPrefixCanonicalMixed.salary hδ w₀ hB apart
      (fun Z=>(cart.exp Z).1.toBorne) (fun Z=>(cart.exp Z).2) soft z cap
  · exact WilsonSeparatedPrefixCanonicalMixed.salary hδ w₀ hB apart
      (fun b=>(cart.flag b).1.toBorne) (fun b=>(cart.flag b).2) hard z cap

end YM.Integration.WilsonSeparatedPrefixCanonicalCarton
end
