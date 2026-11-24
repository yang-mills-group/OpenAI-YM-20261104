import YM.Integration.WilsonPositionProgramTrialCurvatureReading
import YM.Integration.WilsonPositionProgramTrialGroundWords

/-! The entire ground coefficient of the fitted original trial is paid by its
actual numerical fields on an arbitrary even inversion period and at every
position. Both the constant socket and all lower-rank entries participate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialGroundMeasured
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato
open PowerSeries Next.Rank.Normal XSpace PertExtension PertExtension.Orb
open WilsonThermometerPositionTunedSlope (paid finite)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonOriginalStarSceneWords (scalar)
open WilsonMaxwellThermometerGroundInversion (earned)
open WilsonThermometerRegisteredGroundInk (deposited)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
  (place:I→Fin 3)
local notation "F" j:max => R.family.labels.level (d j)

theorem ink (v:∀j,(F j).Coeff)(sites:Fin 3 → Cover)(P:XSpace.Period)(tree:P.Tree):
    coeff 0 (paid R d (frozen R d v) (finite R d P (sites ∘ place) tree))=
      blend (earned (even_iff_two_dvd.mpr P.even) sites) 0
        (deposited R d place 1 1 v (fun (_:I) (_:Unit)=>1) ()):=by
  have re:=WilsonPositionProgramTrialCurvatureReading.original R d v (sites ∘ place) P tree Complex.reCLM 0
  have im:=WilsonPositionProgramTrialCurvatureReading.original R d v (sites ∘ place) P tree Complex.imCLM 0
  simp only [Function.comp_def] at re im
  rw [← WilsonThermometerRegisteredGroundInk.original R d place sites 1 1 v
      (fun (_:I) (_:Unit)=>1) () (even_iff_two_dvd.mpr P.even),←re,←im]
  simpa only [Function.comp_def,Complex.reCLM_apply,Complex.imCLM_apply,mul_comm Complex.I] using
    (Complex.re_add_im _).symm

private theorem one {n:ℕ}(f:Frame G n)(v:f.Coeff)(a:f.Index):
    ‖v a‖≤f.coeffSize v:=by
  exact single_le_sum (f:=fun k=>‖v k‖) (fun _ _=>norm_nonneg _) (mem_univ a)

omit [LinearOrder I] [Fintype I] in
private theorem bound (j:I)(b:Choice R d j):∃c:ℝ,0≤c ∧ ∀v:∀j,(F j).Coeff,
    ‖scalar R d 1 1 v (entry R d j b)‖≤c*(F j).coeffSize (v j):=by
  rcases b with _|s
  · refine ⟨1,zero_le_one,fun v=>?_⟩
    change ‖v j 0‖≤1*(F j).coeffSize (v j)
    simpa only [one_mul] using one (F j) (v j) 0
  refine ⟨‖WilsonOriginalStarLaurentWallet.shape R (d j) s‖,norm_nonneg _,fun v=>?_⟩
  change ‖WilsonOriginalStarLaurentWallet.coefficient R (d j) 1 1 ((F j).core (v j)) s‖≤_
  simp only [WilsonOriginalStarLaurentWallet.coefficient,div_one,one_pow,
    Complex.ofReal_one,one_mul,norm_mul,mul_comm _ ‖WilsonOriginalStarLaurentWallet.shape R (d j) s‖]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  change ‖Function.update (v j) 0 0 s.1‖≤(F j).coeffSize (v j)
  by_cases unit:s.1=0
  · simp only [unit,Function.update_self,norm_zero]
    exact Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  · simpa only [Function.update_of_ne unit] using one (F j) (v j) s.1

private theorem sums {A:Type*}{s t:Finset A}{f g:A→ℝ}
    (hs:∀i,i∈s)(ht:∀i,i∈t)(pay:∀i,f i≤g i):
    ∑i∈s,f i≤∑i∈t,g i:=by
  have h:s=t:=by ext i; exact ⟨fun _=>ht i,fun _=>hs i⟩
  rw [h]
  exact sum_le_sum (fun i _=>pay i)

/-- The same finite constant works for all regulator sides, placements,
submitted numerical vectors and every chosen tree. -/
theorem original : ∃M:ℝ,0≤M ∧ ∀(v:∀j,(F j).Coeff)(sites:Fin 3 → Cover)
    (P:XSpace.Period)(tree:P.Tree),
    ‖coeff 0 (paid R d (frozen R d v) (finite R d P (sites ∘ place) tree))‖≤
      M*∏j,(F j).coeffSize (v j):=by
  choose c cp hc using bound R d
  choose m mp hm using fun b:((j:I)→Choice R d j)=>WilsonPositionProgramTrialGroundWords.original R d b place
  refine ⟨∑b:((j:I)→Choice R d j),m b*∏j,c j (b j),
    sum_nonneg (fun b _=>mul_nonneg (mp b) (prod_nonneg fun j _=>cp j (b j))),?_⟩
  intro v sites P T
  rw [ink,deposited,map_sum,sum_mul]
  apply (norm_sum_le ..).trans
  apply sums
  · simp only [mem_univ,implies_true]
  · simp only [mem_univ,implies_true]
  intro b
  have cost:=hm b (even_iff_two_dvd.mpr P.even) sites 1 1 v (fun _=>1)
  simp only [one_mul,norm_prod] at cost
  rw [mul_assoc,←prod_mul_distrib]
  exact cost.trans (mul_le_mul_of_nonneg_left (prod_le_prod (fun j _=>norm_nonneg _)
    (fun j _=>hc j (b j) v)) (mp b))

end YM.Integration.WilsonPositionProgramTrialGroundMeasured
end
