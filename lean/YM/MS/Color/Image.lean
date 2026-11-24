import YM.MS.Color.Mean

set_option autoImplicit false
noncomputable section
namespace YM.MS.Color
open Function Filter Set Finset Plane Koszul Real Momentum Tensor Submodule MeasureTheory
open Landau Detect Local BV Woven
open Complex (I)
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {A P D: Type} {F: Score G D P}
lemma charge_integral [MeasurableSpace A] (μ : Measure A) [Fintype D] [DecidableEq D]
    (φ : P→Momentum D) (w) {f : A→ Score G D P} (he:∀ i, Integrable (fun x=> f x i) μ) :
    (send φ).raise (fun i=> ∫ x,f x i ∂μ) w=∫ x,(send φ).raise (f x) w ∂μ:= by
   -- recursive also integrability. syntax mean no topology
   suffices hp: Integrable (fun x=> (send φ).raise (f x) w) μ ∧ _ from (hp.2 : (send φ).raise (fun i=> ∫ x,f x i ∂μ) w=∫ x,(send φ).raise (f x) w ∂μ)
   induction w generalizing f with
   | nil=> simp [Charge.raise]
   | cons a w ih=>
       rcases a with ⟨a,p⟩; obtain ⟨hx,h0⟩:= ih (f:=fun x=>Koszul.D (a,p) (f x)) (fun i=>he ((a,p)::i))
       let q i:= (send φ).table a i p
       have hv i: Integrable (fun x=> q i * f x ((i,p)::w)) μ:= (he _).const_mul _
       have ha := integrable_finsetSum Finset.univ fun i _=> hv i
       have hh := hx.const_mul (cross true (Landau.parity a)); simp_rw [Charge.act_at]; refine ⟨ha.add hh,?_⟩
       have ht : (fun i=> ∫ x, Koszul.D (a,p) (f x) i ∂μ)=Koszul.D (a,p) (fun i=>∫ x,f x i ∂μ):=rfl
       rw [integral_add ha hh,integral_finsetSum _ (fun i _=> hv i),← ht,h0, integral_const_mul]; simp_rw [integral_const_mul]; rfl
lemma mean_charge [Fintype D] [DecidableEq D] (f:P→Momentum D) : mean ((send f).raise F)=(send f).raise (mean F) := by
   ext w; rw [mean_def,show (send f).raise (mean F) w= _ from charge_integral G.probHaar (f:=fun u=>repeatC u F) f w (point_mass (F:=F))] ; simp_rw [commute]
lemma mean_sym (hf : Koszul.Symm (field Landau.parity) F) : Koszul.Symm (field Landau.parity) (mean F):= by
    intro l i j k; simp_rw [mean_def,repeat_sym _ hf l i j k, integral_const_mul]
variable [NormedAddCommGroup P] -- not needed for mean_sym
def pale (F:Score G D P) := ((2:ℂ)⁻¹) • (F+overC F)
lemma pale_fixed : overC (pale F)=pale F:= by unfold pale; rw [map_smulₛₗ,map_add,over_cycle,add_comm,map_inv₀,map_ofNat]
lemma pale_sym (hf : Koszul.Symm (field Landau.parity) F) : Koszul.Symm (field Landau.parity) (pale F):= (hf.add (over_sym hf)).smul _
lemma pale_identity (hp:overC F=F): pale F=F:= by unfold pale; rw [hp, ← two_smul ℂ F, smul_smul,inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul]
lemma pale_inside {u:G.El} (h : repeatC u F = F) : repeatC u (pale F)=pale F:= by simp only [pale,map_smul,map_add,h,over_k]
lemma pale_Q {F: Law G}: natQ (pale F) = pale (natQ F):= by
   unfold pale; rw [map_smul,map_add, show overC (natQ F)=natQ (overC F) from over_act id (fun _=>rfl)]
section local'
variable {F: Law G} {h q:ℤ} {r:ℕ}
lemma convert_sig (he:F∈Bed G h q r) : mean F∈Bed G h q r:= momentSpan _ G.probHaar (point_mass (F:=F)) (fun k=>repeat_bed k he)
structure Bright (F: Law G) : Prop where
   weight : sym F
   color (u:G.El) : repeatC u F=F
   shadow : overC F=F
lemma hue (hv:sym F): Bright (pale (mean F)):= ⟨pale_sym (mean_sym hv),fun u=> pale_inside (mean_fixed u), pale_fixed⟩
end local'
end YM.MS.Color
