import YM.Integration.WilsonCapturedPrimaryWardFiring

/-! The genuine hard flag record and all its regular and compulsory entries
survive an independent positive change of units on each incoming marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardCarton
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open MergeProof MergeProof.Accent Push.GridApprox.Nil WilsonCapturedPrimaryWardFiring
open scoped Classical BigOperators
variable {V I Y:Type*} [DecidableEq V] {J:Census V} (b:V→ℝ) {G:Gauge} {n:Side}
local notation "θ" => names J b

theorem borne {o:V→Site n} {p:Support n} {f:Config G n→Poly J} {t:ℝ} (h:Borne o p f t):
    Borne o p (fun U=>θ (f U)) t:=by
  refine ⟨fun U V a c=>congrArg θ (h.home U V a c),fun g U=>congrArg θ (h.turns g U),
    fun i=>(measurable_const.mul (h.me i)),fun U i hi=>?_⟩
  rw [names_part,h.scope U i hi,mul_zero]

theorem rises_iff {x:Poly J} (h:rises x):rises (θ x):=by
  intro i hi
  apply h i
  intro he
  exact hi (by rw [names_part,he,mul_zero])

theorem carton {o:V→Site n} {t:ℝ} {H:Support n→Config G n→Poly J} {K:Box n→Config G n→Poly J}
    (c:Carton o H K t):Carton o (fun i U=>θ (H i U)) (fun i U=>θ (K i U)) t:=by
  constructor
  · intro p
    obtain ⟨a,alive⟩:=c.exp p
    refine ⟨⟨borne b a.toBorne,fun U hu=>a.permits U (fun h0=>hu (by rw [h0,map_zero])),fun U=>?_⟩,
      fun U=>rises_iff b (alive U)⟩
    rw [names_part,a.sil U,mul_zero]
  · intro p
    obtain ⟨a,alive⟩:=c.flag p
    exact ⟨⟨borne b a.toBorne,fun U hu=>a.permits U (fun h0=>hu (by rw [h0,map_zero]))⟩,
      fun U=>rises_iff b (alive U)⟩

theorem loci (hb:∀i,0<b i) {w:V→ℝ} {F:Y→Poly J} {a:ℝ} (h:Loci w F a):
    Loci (fun i=>w i/b i) (fun U=>θ (F U)) a:=by
  obtain ⟨s,hs,bounds,bill⟩:=h
  have pos (i:J.Mode):0≤Poly.toll b i:=(Poly.worth hb i).le
  refine ⟨fun i=>Poly.toll b i*s i,fun i=>mul_nonneg (pos i) (hs i),fun U i=>?_,?_⟩
  · rw [names_part,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pos i)]
    exact mul_le_mul_of_nonneg_left (bounds U i) (pos i)
  · apply le_trans _ bill
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    rw [←mul_assoc,WilsonCapturedPrimaryWardFiring.toll J b hb]

theorem towed (hb:∀i,0<b i) {w:V→ℝ} {X:I→Support n} {F:I→Y→Poly J} {B:ℕ} {e C:ℝ} (h:Towed w X F B e C):
    Towed (fun i=>w i/b i) X (fun i U=>θ (F i U)) B e C:=by
  obtain ⟨a,summed,hit,bound⟩:=h
  exact ⟨a,summed,hit,fun i=>loci b hb (bound i)⟩

theorem covering (z:Support n) (f:Box n→Poly J):
    θ (field f z)=field (fun p=>θ (f p)) z:=by
  unfold field
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  unfold grid
  split_ifs
  · exact map_prod θ _ _
  · exact map_zero θ

theorem restore_names [Fintype V] (R:Rep G n) (Φ:V→Config G n→ℂ) (P:V→Box n→Config G n→ℂ)
    (H:Support n→Config G n→Poly J) (K:Box n→Config G n→Poly J) (U:Config G n):
    θ (restore R Φ P H K U)=restore R (fun i U=>(b i:ℂ)*Φ i U) (fun i p U=>(b i:ℂ)*P i p U)
      (fun i U=>θ (H i U)) (fun p U=>θ (K p U)) U:=by
  simp only [restore,map_smul,map_mul,passing,map_add,map_sum,signal,covering,bar,names_bead]

theorem original [Fintype V] (hb:∀i,0<b i) (R:Rep G n) {Φ:V→Config G n→ℂ} {P:V→Box n→Config G n→ℂ}
    {X:Config G n→Poly J} {o:V→Site n} {w:V→ℝ} {e C:ℝ} (h:Served R Φ P X o w e C):
    Served R (fun i U=>(b i:ℂ)*Φ i U) (fun i p U=>(b i:ℂ)*P i p U) (fun U=>θ (X U))
      o (fun i=>w i/b i) e C:=by
  obtain ⟨H,K,admitted,hr,hf,eq⟩:=h
  exact ⟨_,_,carton b admitted,towed b hb hr,towed b hb hf,funext fun U=>by rw [eq,restore_names]⟩

end YM.Integration.WilsonCapturedPrimaryWardCarton
